module

public import Paid.PDCompute_SolverRegionMemory_076
public import Paid.PDMenu_ComputeFrame_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def denseWriteBlockCode : ℕ → ℕ → List Instruction
  | _,0 => []
  | source,count+1 => denseWriteCellCode source++denseWriteBlockCode (source+1) count

theorem denseWriteBlockCode_length (source count : ℕ) : (denseWriteBlockCode source count).length=6*count := by
  induction count generalizing source with
  | zero => rfl
  | succ count ih => simp only [denseWriteBlockCode,List.length_append,denseWriteCellCode_length,ih]; omega

/-- Actual fixed six-cell table-entry writer, generalized over finite
code generation for proof reuse. All previous dense cells outside this
entry are protected at EVERY actual state, even inside solver workspace. -/
theorem denseWriteBlock_trace (program : Program) (input : List Cell) (cells : List Cell)
    (before : State) (base source pointer : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (room : source+cells.length ≤ headerWords)
    (hbase : before.register .fresh=.natural base) (hpointer : before.register .old=.natural pointer)
    (contents : ∀ (offset : ℕ) (inside : offset < cells.length),values (source+offset)=cells[offset])
    (outside : ∀ offset < cells.length, pointer+offset < base ∨ base+headerWords ≤ pointer+offset)
    (fetched : FetchesCode program before.pc (denseWriteBlockCode source cells.length)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 105*cells.length+15 ∧
      Header after base values ∧ PDLower.CalibrationCompute.HeapList after pointer cells ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+cells.length) ∧
      after.pc=before.pc+6*cells.length ∧ after.output=before.output ∧
      ∀ state ∈ trace, RegionMemory before state (cellRegion pointer cells.length) := by
  induction cells generalizing before source pointer with
  | nil =>
    refine ⟨[before],before,rfl,rfl,.singleton before,?_,header,?_,hbase,?_,rfl,rfl,?_⟩
    · exact time_singleton_le program before
    · apply PDLower.CalibrationCompute.HeapList.of_values <;> intro offset inside <;> simp at inside
    · simpa only [List.length_nil,Nat.add_zero] using hpointer
    · intro state member
      have same : state=before := by simpa only [List.mem_singleton] using member
      subst state
      exact RegionMemory.refl before _
  | cons cell cells ih =>
    have inside : source < headerWords := by simp only [List.length_cons] at room; omega
    let first:=denseWriteCellResult before base source pointer
    have fetchFirst : FetchesCode program before.pc (denseWriteCellCode source) := by
      rw [List.length_cons,denseWriteBlockCode] at fetched
      exact fetched.append_left
    obtain ⟨firstTrace,firstHead,firstLast,firstChain,firstTime,firstMemory⟩ :=
      denseWriteCell_trace program input before base source pointer values header inside hbase hpointer fetchFirst
    have firstHeader : Header first base values := denseWriteCellResult_header before base source pointer values header
      (by simpa only [Nat.add_zero] using outside 0 (by simp))
    have firstBase : first.register .fresh=.natural base := hbase
    have firstPointer : first.register .old=.natural (pointer+1) := rfl
    have firstPC : first.pc=before.pc+6 := rfl
    have firstValue : first.heap pointer=cell := by
      change Function.update before.heap pointer (before.heap (base+source)) pointer=cell
      rw [Function.update_self,header.value source inside]
      have value:=contents 0 (by simp)
      change values (source+0)=cell at value
      exact value
    have tailContents : ∀ (offset : ℕ) (bound : offset < cells.length),values (source+1+offset)=cells[offset] := by
      intro offset bound
      have value:=contents (offset+1) (by simp only [List.length_cons]; omega)
      change values (source+(offset+1))=cells[offset] at value
      simpa only [Nat.add_assoc,Nat.add_comm 1 offset] using value
    have tailOutside : ∀ offset < cells.length, pointer+1+offset < base ∨ base+headerWords ≤ pointer+1+offset := by
      intro offset bound
      have addressEq : pointer+1+offset=pointer+(offset+1) := by omega
      rw [addressEq]
      exact outside (offset+1) (by simp only [List.length_cons]; omega)
    have fetchTail : FetchesCode program first.pc (denseWriteBlockCode (source+1) cells.length) := by
      rw [List.length_cons,denseWriteBlockCode] at fetched
      exact fetched.append_right
    have tailRoom : source+1+cells.length ≤ headerWords := by simp only [List.length_cons] at room; omega
    obtain ⟨tail,after,tailHead,tailLast,tailChain,tailTime,afterHeader,tailHeap,afterBase,afterPointer,afterPC,afterOutput,tailMemory⟩ :=
      ih first (source+1) (pointer+1) firstHeader tailRoom firstBase firstPointer tailContents tailOutside fetchTail
    have tailFinalMemory:=RegionMemory.trace_last tailMemory tailLast
    have firstRegion : ∀ state ∈ firstTrace, RegionMemory before state (cellRegion pointer (cells.length+1)) := by
      intro state member
      exact (firstMemory state member).region ((mem_cellRegion_iff pointer (cells.length+1) pointer).mpr (by omega))
    have tailRegion : ∀ state ∈ tail, RegionMemory first state (cellRegion pointer (cells.length+1)) := by
      intro state member
      exact (tailMemory state member).enlarge (cellRegion_tail_subset pointer cells.length)
    have joined:=joinTrace_spec program input firstTrace tail before first after 105 (105*cells.length+15)
      firstHead firstLast tailHead tailLast firstChain tailChain firstTime tailTime
    refine ⟨joinTrace firstTrace tail,after,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,?_,afterBase,?_,?_,
      afterOutput,RegionMemory.join_trace firstTrace tail before first _ firstLast firstRegion tailRegion⟩
    · simp only [List.length_cons]
      have bound:=joined.2.2.2
      omega
    · apply PDLower.CalibrationCompute.HeapList.of_values
      · intro offset bound
        cases offset with
        | zero =>
          simp only [Nat.add_zero]
          apply tailFinalMemory.2.2.1
          exact Finset.mem_insert_self _ _
        | succ offset =>
          have live:=tailHeap.1 offset (by simp only [List.length_cons] at bound; omega)
          have addressEq : pointer+Nat.succ offset=pointer+1+offset := by omega
          rw [addressEq]
          exact live
      · intro offset bound
        cases offset with
        | zero =>
          change after.heap (pointer+0)=cell
          rw [Nat.add_zero,tailFinalMemory.1 pointer (by rw [mem_cellRegion_iff]; omega)]
          exact firstValue
        | succ offset =>
          have offsetBound : offset < cells.length := by simp only [List.length_cons] at bound; omega
          have value:=PDLower.CalibrationCompute.HeapList.value tailHeap offset offsetBound
          change after.heap (pointer+Nat.succ offset)=cells[offset]
          have addressEq : pointer+Nat.succ offset=pointer+1+offset := by omega
          rw [addressEq]
          exact value
    · rw [afterPointer]
      simp only [List.length_cons]
      congr 1
      omega
    · rw [afterPC,firstPC]
      simp only [List.length_cons]
      omega

end PDCompute.Solver
