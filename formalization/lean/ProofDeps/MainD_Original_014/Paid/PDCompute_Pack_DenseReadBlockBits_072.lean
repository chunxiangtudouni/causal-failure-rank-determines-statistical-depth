module
public import Paid.PDCompute_Pack_DenseReadCellBits_070
public import Paid.PDCompute_SolverDenseBlock_071

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

theorem denseReadBlock_trace_safe (program : Program) (input : List Cell) (cells : List Cell)
    (before : State) (base start pointer n k budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (room : start+cells.length ≤ headerWords)
    (hbase : before.register .fresh=.natural base) (hpointer : before.register .old=.natural pointer)
    (source : PDLower.CalibrationCompute.HeapList before pointer cells)
    (outside : ∀ offset < cells.length, pointer+offset < base ∨ base+headerWords ≤ pointer+offset)
    (safe : SafeBits before budget)
    (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (pointerBits : 1+natBits (pointer+cells.length) ≤ budget)
    (counter : natBits (before.pc+6*cells.length) ≤ budget)
    (fetched : FetchesCode program before.pc (denseReadBlockCode start cells.length)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 105*cells.length+15 ∧
      Header after base (denseReadHeaderValues cells start values) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+cells.length) ∧
      after.pc=before.pc+6*cells.length ∧ Frame before after base n k ∧
      after.output=before.output ∧ (∀ state ∈ trace, HeaderMemory before state base) ∧
      (∀ state∈trace,SafeBits state budget) := by
  induction cells generalizing before values start pointer with
  | nil =>
    refine ⟨[before],before,rfl,rfl,.singleton before,?_,header,hbase,?_,rfl,?_,rfl,?_,?_⟩
    · exact time_singleton_le program before
    · simpa only [List.length_nil,Nat.add_zero] using hpointer
    · exact ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩
    · intro state member
      have eq : state=before := by simpa only [List.mem_singleton] using member
      subst state
      exact HeaderMemory.refl before base
    · intro state member
      have eq : state=before:=by simpa only [List.mem_singleton] using member
      subst state
      exact safe
  | cons cell cells ih =>
    have inside : start < headerWords := by simp only [List.length_cons] at room; omega
    let first := denseReadCellResult before base start pointer
    have fetchFirst : FetchesCode program before.pc (denseReadCellCode start) := by
      rw [List.length_cons,denseReadBlockCode] at fetched
      exact fetched.append_left
    have firstPointerBits : 1+natBits (pointer+1) ≤ budget:=
      (Nat.add_le_add_left (natBits_mono (by simp only [List.length_cons];omega : pointer+1 ≤ pointer+(cell::cells).length)) 1).trans pointerBits
    have firstCounter : natBits (before.pc+6) ≤ budget:=
      (natBits_mono (by simp only [List.length_cons];omega : before.pc+6 ≤ before.pc+6*(cell::cells).length)).trans counter
    obtain ⟨firstTrace,firstHead,firstLast,firstChain,firstTime,firstMemory,firstBits⟩ :=
      denseReadCell_trace_safe program input before base start pointer budget values header inside hbase hpointer
        (by simpa only [Nat.add_zero] using source.1 0 (by simp)) safe (addressBits start inside) firstPointerBits firstCounter fetchFirst
    have fields:=denseReadCellResult_fields before base start pointer
    have firstHeader:=header.denseReadCell start pointer
    have firstBase : first.register .fresh=.natural base:=fields.2.2.1.trans hbase
    have firstPointer : first.register .old=.natural (pointer+1):=fields.2.2.2.1
    have firstPC : first.pc=before.pc+6:=fields.2.2.2.2.1
    have firstFrame : Frame before first base n k:=slotWrite_frame before first base start n k (before.heap pointer) inside fields.1 fields.2.1
    have firstSafe : SafeBits first budget:=firstBits first (List.mem_of_getLast? firstLast)
    have cellValue : before.heap pointer=cell := by
      have lookup := PDLower.CalibrationCompute.HeapList.value source 0 (by simp)
      change before.heap (pointer+0)=cell at lookup
      exact lookup
    rw [cellValue] at firstHeader
    have frame := HeaderMemory.trace_last firstMemory firstLast
    have tailSource : PDLower.CalibrationCompute.HeapList first (pointer+1) cells := by
      apply PDLower.CalibrationCompute.HeapList.of_values
      · intro offset bound
        have addressEq : pointer+1+offset=pointer+(offset+1) := by omega
        rw [addressEq,frame.2.1]
        exact source.1 (offset+1) (by simp only [List.length_cons]; omega)
      · intro offset bound
        have addressEq : pointer+1+offset=pointer+(offset+1) := by omega
        rw [addressEq,frame.1 _ (outside (offset+1) (by simp only [List.length_cons]; omega))]
        have lookup := PDLower.CalibrationCompute.HeapList.value source (offset+1)
          (by simp only [List.length_cons]; omega)
        change before.heap (pointer+(offset+1))=cells[offset] at lookup
        exact lookup
    have tailOutside : ∀ offset < cells.length, pointer+1+offset < base ∨ base+headerWords ≤ pointer+1+offset := by
      intro offset bound
      have addressEq : pointer+1+offset=pointer+(offset+1) := by omega
      rw [addressEq]
      exact outside (offset+1) (by simp only [List.length_cons]; omega)
    have fetchTail : FetchesCode program first.pc (denseReadBlockCode (start+1) cells.length) := by
      rw [List.length_cons,denseReadBlockCode] at fetched
      exact fetched.append_right
    have tailRoom : start+1+cells.length ≤ headerWords := by simp only [List.length_cons] at room; omega
    have tailPointerBits : 1+natBits (pointer+1+cells.length) ≤ budget:=by
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 cells.length] using pointerBits
    have tailCounter : natBits (first.pc+6*cells.length) ≤ budget:=by
      rw [firstPC]
      simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm 6 (6*cells.length)] using counter
    obtain ⟨tail,after,tailHead,tailLast,tailChain,tailTime,afterHeader,afterBase,afterPointer,afterPC,afterFrame,afterOutput,tailMemory,tailBits⟩ :=
      ih first (start+1) (pointer+1) (Function.update values start cell) firstHeader tailRoom
        firstBase firstPointer tailSource tailOutside firstSafe tailPointerBits tailCounter fetchTail
    have joined := joinTrace_spec program input firstTrace tail before first after 105 (105*cells.length+15)
      firstHead firstLast tailHead tailLast firstChain tailChain firstTime tailTime
    refine ⟨joinTrace firstTrace tail,after,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,afterBase,?_,?_,
      firstFrame.trans afterFrame,afterOutput.trans frame.2.2,
      joinTrace_memory firstTrace tail before first base firstLast firstMemory tailMemory,
      joinTrace_invariant firstTrace tail (fun state=>SafeBits state budget) firstBits tailBits⟩
    · simp only [List.length_cons]
      have bound := joined.2.2.2
      omega
    · rw [afterPointer]
      simp only [List.length_cons]
      congr 1
      omega
    · rw [afterPC,firstPC]
      simp only [List.length_cons]
      omega


end PDCompute.Pack
