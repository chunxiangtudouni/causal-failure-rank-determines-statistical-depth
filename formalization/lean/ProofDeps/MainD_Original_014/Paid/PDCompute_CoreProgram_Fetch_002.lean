module

public import Paid.PDCompute_CoreProgram_GenericFetch_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.CoreProgram

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open RootD27.Core PDCompute.Solver

attribute [local irreducible] matrixCode solverCalleeCode PDLower.CalibrationCompute.kernel
  PDCompute.CorePrelude.program program code suffix calleeCode bodyCode loopCode finalCode

/-- All fetches below come from this ONE concrete fixed program. -/
theorem whole_fetch : FetchesCode program 0 program.toList := Generic.array_fetch program

/-- The unchanged Prelude is decoded from its own program_toList;
neither a replacement ROM nor an auxiliary successful run is assumed. -/
theorem prelude_fetch :
    FetchesCode program 0 (inputCopyCode 13) ∧
    FetchesCode program 39 (endpointHeapOutputCode 39 48 96 302) ∧
    FetchesCode program 302 (calibrationHeapArgumentsCode PDCompute.CorePrelude.afterCalibration) ∧
    FetchesCode program 316 (PDLower.CalibrationCompute.kernel 316).toList ∧
    FetchesCode program PDCompute.CorePrelude.afterCalibration
      (PDCompute.CorePrelude.headerCode PDCompute.CorePrelude.afterCalibration) ∧
    FetchesCode program initializationPC suffix := by
  unfold program initializationPC
  exact Generic.prelude_fetch suffix

theorem endpoint_fetch :
    FetchesCode program 39 (endpointHeapArgumentsCode 48 96 295) ∧
    FetchesCode program labels.endpointEntry (RootD27.Endpoint.endpointCode labels.endpointEntry) ∧
    FetchesCode program 295 (emitHeapCode 295 302) := by
  have literal:=prelude_fetch.2.1
  change FetchesCode program 39 (endpointHeapArgumentsCode 48 96 295++
    (RootD27.Endpoint.endpointCode 52++emitHeapCode 295 302)) at literal
  refine ⟨literal.append_left,?_,?_⟩
  · simpa only [endpointHeapArguments_length,fixed_labels.2.2.1] using literal.append_right.append_left
  · simpa only [endpointHeapArguments_length,RootD27.Endpoint.endpointCode_length] using literal.append_right.append_right

theorem calibration_fetch : FetchesCode program labels.calibrationEntry
    (PDLower.CalibrationCompute.kernel labels.calibrationEntry).toList :=
  prelude_fetch.2.2.2.1

/-- The real continuation splits into initialization164, original529
outer loop, final252, common stub1 and the full original solver body. -/
theorem suffix_fetch :
    FetchesCode program initializationPC (initializeSearchCode initializationPC solveEntry) ∧
    FetchesCode program outerPC loopCode ∧
    FetchesCode program selectorPC finalCode ∧
    program[solveEntry]?=some (.jump (solveEntry+1)) ∧
    FetchesCode program (solveEntry+1) calleeCode := by
  have literal:=prelude_fetch.2.2.2.2.2
  unfold suffix at literal
  exact Generic.suffix_fetch program initializationPC outerPC selectorPC solveEntry loopCode finalCode calleeCode
    literal loop_length final_length static_bounds.2.1 static_bounds.2.2.1 static_bounds.2.2.2.1

theorem initialization_fetch : FetchesCode program initializationPC
    (initializeSearchCode initializationPC labels.solveEntry) := suffix_fetch.1

theorem outer_fetch : FetchesCode program outerPC (PDCompute.CoreSearchLoop.code outerPC bodyCode) :=
  by
    have fetched:=suffix_fetch.2.1
    unfold loopCode at fetched
    exact fetched

theorem body_fetch : FetchesCode program bodyOrigin
    (bisectionBodyCode bodyOrigin labels.solveEntry decrementOrigin) := by
  have fetched:=PDCompute.CoreSearchLoop.body_fetch program outerPC bodyCode outer_fetch
  rw [loop_addresses.1] at fetched
  unfold bodyCode at fetched
  exact fetched

theorem decrement_fetch : FetchesCode program decrementOrigin PDCompute.CoreSearchLoop.decrementCode := by
  rw [←loop_addresses.2.1]
  exact PDCompute.CoreSearchLoop.decrement_fetch program outerPC bodyCode outer_fetch

theorem back_fetch : program[backOrigin]?=some (.jump outerPC) := by
  rw [←loop_addresses.2.2.1]
  exact PDCompute.CoreSearchLoop.back_fetch program outerPC bodyCode outer_fetch

theorem final_fetch :
    FetchesCode program selectorPC (finalSelectorCode selectorPC) ∧
    FetchesCode program tailPC (PDCompute.CoreFinalTail.code tailPC) := by
  have fetched:=suffix_fetch.2.2.1
  rw [final_split] at fetched
  exact ⟨fetched.append_left,by simpa only [finalSelector_length,tailPC] using fetched.append_right⟩

theorem halt_fetch : program[haltPC]?=some .halt :=
  PDCompute.CoreFinalTail.halt_fetch program tailPC final_fetch.2

theorem stub_fetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)) := suffix_fetch.2.2.2.1

theorem solver_fetch : FetchesCode program (labels.solveEntry+1)
    (solverCalleeCode .liveHeap (labels.solveEntry+1)) := by
  have fetched:=suffix_fetch.2.2.2.2
  unfold calleeCode at fetched
  exact fetched

/-- Actual fixed epilogue marker, before the fetched jumpIndirect.old;
no caller continuation PC or free end-of-file is substituted for it. -/
theorem solver_marker_fetch : program[labels.solveReturn]?=some (.jumpIndirect .old) := by
  exact Generic.marker_fetch program solveEntry solver_fetch

end PDCompute.CoreProgram
