module

public import Paid.PDCompute_SolverDenseReadTrace_057
public import Paid.PDCompute_SolverMemoryJoin_062

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def denseReadBlockCode : ℕ → ℕ → List Instruction
  | _,0 => []
  | start,count+1 => denseReadCellCode start++denseReadBlockCode (start+1) count

def denseReadHeaderValues : List Cell → ℕ → (ℕ → Cell) → (ℕ → Cell)
  | [],_,values => values
  | cell::cells,start,values => denseReadHeaderValues cells (start+1) (Function.update values start cell)

theorem denseReadBlockCode_length (start count : ℕ) : (denseReadBlockCode start count).length=6*count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [denseReadBlockCode,List.length_append,denseReadCellCode_length,ih]; omega

/-- A fixed six-cell instance genuinely loads a previous dense entry;
the general list statement is a verified finite code-generation lemma.
Source cells lie outside Header48 and remain unchanged throughout. -/
theorem denseReadBlock_trace (program : Program) (input : List Cell) (cells : List Cell)
    (before : State) (base start pointer n k : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (room : start+cells.length ≤ headerWords)
    (hbase : before.register .fresh=.natural base) (hpointer : before.register .old=.natural pointer)
    (source : PDLower.CalibrationCompute.HeapList before pointer cells)
    (outside : ∀ offset < cells.length, pointer+offset < base ∨ base+headerWords ≤ pointer+offset)
    (fetched : FetchesCode program before.pc (denseReadBlockCode start cells.length)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 105*cells.length+15 ∧
      Header after base (denseReadHeaderValues cells start values) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+cells.length) ∧
      after.pc=before.pc+6*cells.length ∧ Frame before after base n k ∧
      after.output=before.output ∧ ∀ state ∈ trace, HeaderMemory before state base := by
  induction cells generalizing before values start pointer with
  | nil =>
    refine ⟨[before],before,rfl,rfl,.singleton before,?_,header,hbase,?_,rfl,?_,rfl,?_⟩
    · exact time_singleton_le program before
    · simpa only [List.length_nil,Nat.add_zero] using hpointer
    · exact ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩
    · intro state member
      have eq : state=before := by simpa only [List.mem_singleton] using member
      subst state
      exact HeaderMemory.refl before base
  | cons cell cells ih =>
    have inside : start < headerWords := by simp only [List.length_cons] at room; omega
    let first := denseReadCellResult before base start pointer
    have fetchFirst : FetchesCode program before.pc (denseReadCellCode start) := by
      rw [List.length_cons,denseReadBlockCode] at fetched
      exact fetched.append_left
    obtain ⟨firstTrace,firstHead,firstLast,firstChain,firstTime,firstHeader,firstBase,firstPointer,firstPC,firstFrame,firstMemory⟩ :=
      denseReadCell_trace program input before base start pointer n k values header inside hbase hpointer
        (by simpa only [Nat.add_zero] using source.1 0 (by simp)) fetchFirst
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
    obtain ⟨tail,after,tailHead,tailLast,tailChain,tailTime,afterHeader,afterBase,afterPointer,afterPC,afterFrame,afterOutput,tailMemory⟩ :=
      ih first (start+1) (pointer+1) (Function.update values start cell) firstHeader tailRoom
        firstBase firstPointer tailSource tailOutside fetchTail
    have joined := joinTrace_spec program input firstTrace tail before first after 105 (105*cells.length+15)
      firstHead firstLast tailHead tailLast firstChain tailChain firstTime tailTime
    refine ⟨joinTrace firstTrace tail,after,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,afterBase,?_,?_,
      firstFrame.trans afterFrame,afterOutput.trans frame.2.2,
      joinTrace_memory firstTrace tail before first base firstLast firstMemory tailMemory⟩
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

end PDCompute.Solver
