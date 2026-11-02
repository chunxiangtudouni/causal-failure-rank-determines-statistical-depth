module
public import Paid.PDCompute_CoreRun_Prefix_002
public import PaperProofs.Paid.PDCompute_Codec_001
public import Paid.PDLower_CalibrationCompute_Standalone_081

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
@[expose] public section
namespace PDCompute.CoreRun
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

attribute [local irreducible] matrixCode solverCalleeCode PDLower.CalibrationCompute.kernel
  PDCompute.CorePrelude.program PDCompute.CorePrelude.bodyStart PDCompute.CorePrelude.afterCalibration
  initializeSearchCode bisectionBodyCode finalizationCode PDCompute.CoreSearchLoop.code
  PDCompute.CoreProgram.program PDCompute.CoreProgram.suffix PDCompute.CoreProgram.calleeCode
  PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.solveEntry PDCompute.CoreProgram.solveReturn
  PDCompute.CoreProgram.labels PDCompute.CoreProgram.pcUpper

def bitsConstant : ℕ := 134217728+2*natBits PDCompute.CoreProgram.pcUpper+256

theorem artifact_stream (P : Parameters) (fee : ℚ) :
    (encodeList encodeEndpoint P.endpointCache.toList++
      encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList)++
        PDCompute.CoreSuffix.emittedCells P fee=encodeArtifact (buildArtifact P fee) := by
  simp only [PDCompute.CoreSuffix.emittedCells,encodeArtifact,buildArtifact,encodeFrontend,
    buildCachedFrontend,List.append_assoc]

/-- A real fixed-machine run, with exact provenance of its prefix and
main trace. Early counts are equality transports, not extra input facts. -/
structure Result (P : Parameters) (fee : ℚ) (front : PrefixResult P fee) where
  trace : List State
  main : List State
  after : State
  joined : trace=joinTrace front.trace main
  mainHead : main.head?=some front.after
  mainLast : main.getLast?=some after
  mainLower : ∀ state∈main,PDCompute.CoreProgram.initializationPC≤state.pc
  run : Runs PDCompute.CoreProgram.program (preparedInput P fee) trace after
  output : after.output=encodeArtifact (buildArtifact P fee)
  decoded : decodeArtifact after.output=some (buildArtifact P fee)
  timeBound : time PDCompute.CoreProgram.program trace≤300000*sourceCoreScale P fee
  space : peakCells trace≤512*sourceRecordSpace P
  safe : ∀ state∈trace,RootD27.Bits.SafeBits state (PDCompute.CoreGlobalBudget.budget P fee PDCompute.CoreProgram.pcUpper)
  bits : peakOperandBits trace≤bitsConstant*coreOperandBound P fee
  requests : actualSolveRequests PDCompute.CoreProgram.labels trace=
    (P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2
  countExact : PaperProofs.Paid.Computation.entryCount PDCompute.CoreProgram.labels.solveEntry trace=
    (actualSolveRequests PDCompute.CoreProgram.labels trace).length
  countBound : PaperProofs.Paid.Computation.entryCount PDCompute.CoreProgram.labels.solveEntry trace≤P.bisectionBudget fee+2
  endpointCount : PaperProofs.Paid.Computation.entryCount PDCompute.CoreProgram.labels.endpointEntry trace=
    PaperProofs.Paid.Computation.entryCount 52 front.trace
  calibrationCount : PaperProofs.Paid.Computation.entryCount PDCompute.CoreProgram.labels.calibrationEntry trace=
    PaperProofs.Paid.Computation.entryCount 316 front.trace
  refinement : SolverCallRefinement PDCompute.CoreProgram.program PDCompute.CoreProgram.labels P fee 40000 trace
  pc : after.pc=PDCompute.CoreProgram.initializationPC+944
  halt : PDCompute.CoreProgram.program[after.pc]?=some .halt
  stopped : step PDCompute.CoreProgram.program (preparedInput P fee) after=none

theorem callee_room_transfer (entry target upper : ℕ) (same : target=entry)
    (bound : (solverCalleeCode .liveHeap (entry+1)).length≤upper) :
    (solverCalleeCode .liveHeap (target+1)).length≤upper := by
  rw [same]
  exact bound

/-- The actual shared callee and whole945 fetch are supplied by the ONE
frozen fixed program, not by new per-input code or a successful-run oracle. -/
theorem main_actual (P : Parameters) (fee : ℚ) (front : PrefixResult P fee) :
    Nonempty (PDCompute.CoreSuffix.Result PDCompute.CoreProgram.program PDCompute.CoreProgram.labels
      (preparedInput P fee) P fee PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.pcUpper front.after) := by
  have geometry:=PDCompute.CoreProgram.static_bounds
  have labels:=PDCompute.CoreProgram.fixed_labels
  have entryEnd:=main_end
  have solverOrigin : PDCompute.CoreProgram.labels.solveEntry+1≤PDCompute.CoreProgram.pcUpper := by omega
  have length:=geometry.2.2.2.2.2.2.2.2.2.1
  unfold PDCompute.CoreProgram.calleeCode at length
  have solverLength:=callee_room_transfer PDCompute.CoreProgram.solveEntry PDCompute.CoreProgram.labels.solveEntry
    PDCompute.CoreProgram.pcUpper labels.1 length
  obtain ⟨main⟩:=PDCompute.CoreSuffix.actual P fee PDCompute.CoreProgram.program PDCompute.CoreProgram.labels
    (preparedInput P fee) PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.pcUpper front.after front.pc front.ready
    (front.safe front.after (List.mem_of_getLast? front.last)) (by omega) entryEnd.le solverOrigin solverLength
    PDCompute.CoreProgram.marker_label main_fetch PDCompute.CoreProgram.stub_fetch PDCompute.CoreProgram.solver_fetch
  exact ⟨main⟩

end PDCompute.CoreRun
