module

public import Paid.PDCompute_CoreProgram_Layout_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDCompute.CoreProgram.Generic

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open RootD27.Core PDCompute.Solver

attribute [local irreducible] matrixCode solverCalleeCode PDLower.CalibrationCompute.kernel PDCompute.CorePrelude.program

/-- Prove the array/list identity with an abstract RAM, before any fixed
main suffix is substituted into the theorem. -/
theorem array_fetch (ram : Program) : FetchesCode ram 0 ram.toList := by
  intro offset _inside
  simp only [Nat.zero_add,Array.getElem?_toList]

/-- The original Prelude's fetch decomposition is proved once for an
arbitrary suffix; the full fixed main/solver array is never normalized. -/
theorem prelude_fetch (tail : List Instruction) :
    FetchesCode (PDCompute.CorePrelude.program tail.toArray) 0 (inputCopyCode 13) ∧
    FetchesCode (PDCompute.CorePrelude.program tail.toArray) 39 (endpointHeapOutputCode 39 48 96 302) ∧
    FetchesCode (PDCompute.CorePrelude.program tail.toArray) 302
      (calibrationHeapArgumentsCode PDCompute.CorePrelude.afterCalibration) ∧
    FetchesCode (PDCompute.CorePrelude.program tail.toArray) 316 (PDLower.CalibrationCompute.kernel 316).toList ∧
    FetchesCode (PDCompute.CorePrelude.program tail.toArray) PDCompute.CorePrelude.afterCalibration
      (PDCompute.CorePrelude.headerCode PDCompute.CorePrelude.afterCalibration) ∧
    FetchesCode (PDCompute.CorePrelude.program tail.toArray) PDCompute.CorePrelude.bodyStart tail := by
  have literal:=array_fetch (PDCompute.CorePrelude.program tail.toArray)
  rw [PDCompute.CorePrelude.program_toList] at literal
  refine ⟨literal.append_left,?_,?_,?_,?_,?_⟩
  · simpa only [inputCopy_length,Nat.zero_add] using literal.append_right.append_left
  · simpa only [inputCopy_length,endpointHeapOutput_length,Nat.zero_add] using
      literal.append_right.append_right.append_left
  · simpa only [inputCopy_length,endpointHeapOutput_length,calibrationHeapArguments_length,Nat.zero_add] using
      literal.append_right.append_right.append_right.append_left
  · simpa only [inputCopy_length,endpointHeapOutput_length,calibrationHeapArguments_length,
      Array.length_toList,Nat.zero_add,PDCompute.CorePrelude.afterCalibration,preparedCalibrationReturnPC] using
      literal.append_right.append_right.append_right.append_right.append_left
  · simpa only [inputCopy_length,endpointHeapOutput_length,calibrationHeapArguments_length,
      Array.length_toList,PDCompute.CorePrelude.header_length,Nat.zero_add,PDCompute.CorePrelude.bodyStart,
      PDCompute.CorePrelude.afterCalibration,preparedCalibrationReturnPC] using
      literal.append_right.append_right.append_right.append_right.append_right

/-- Only abstract lists, addresses and a RAM occur in the decomposition.
Its fetch premise is paid by the concrete Prelude theorem above. -/
theorem suffix_fetch (ram : Program) (start outer selected entry : ℕ)
    (loop final callee : List Instruction)
    (literal : FetchesCode ram start (initializeSearchCode start entry++
      (loop++(final++([.jump (entry+1)]++callee)))))
    (loopLength : loop.length=529) (finalLength : final.length=252)
    (outerPosition : start+164=outer) (finalPosition : outer+529=selected)
    (entryPosition : selected+252=entry) :
    FetchesCode ram start (initializeSearchCode start entry) ∧
    FetchesCode ram outer loop ∧ FetchesCode ram selected final ∧
    ram[entry]?=some (.jump (entry+1)) ∧ FetchesCode ram (entry+1) callee := by
  have loopFetch : FetchesCode ram outer (loop++(final++([.jump (entry+1)]++callee))) := by
    simpa only [initializeSearch_length,outerPosition] using literal.append_right
  have finalFetch : FetchesCode ram selected (final++([.jump (entry+1)]++callee)) := by
    simpa only [loopLength,finalPosition] using loopFetch.append_right
  have solverFetch : FetchesCode ram entry ([.jump (entry+1)]++callee) := by
    simpa only [finalLength,entryPosition] using finalFetch.append_right
  refine ⟨literal.append_left,loopFetch.append_left,finalFetch.append_left,?_,?_⟩
  · simpa only [Nat.add_zero,List.getElem?_cons_zero] using solverFetch.append_left 0 (by change 0<1;decide)
  · simpa only [List.length_cons,List.length_nil] using solverFetch.append_right

theorem marker_fetch (ram : Program) (entry : ℕ)
    (fetched : FetchesCode ram (entry+1) (solverCalleeCode .liveHeap (entry+1))) :
    ram[(entry+1)+46+(matrixCode .liveHeap (entry+1+46)).length+232]?=some (.jumpIndirect .old) := by
  have pack:=solverCallee_matrixPack_fetch .liveHeap ram (entry+1) fetched
  exact PDCompute.Pack.indirect_return_fetch ram _ pack.append_right

end PDCompute.CoreProgram.Generic
