module
public import Paid.PDCompute_CoreRun_Link_001
public import Paid.PDCompute_CorePrelude_Resources_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
@[expose] public section
namespace PDCompute.CoreRun
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

attribute [local irreducible] matrixCode solverCalleeCode PDLower.CalibrationCompute.kernel
  PDCompute.CorePrelude.program PDCompute.CorePrelude.bodyStart PDCompute.CorePrelude.afterCalibration
  PDCompute.CoreProgram.program PDCompute.CoreProgram.suffix PDCompute.CoreProgram.calleeCode
  PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.solveEntry PDCompute.CoreProgram.solveReturn
  PDCompute.CoreProgram.labels PDCompute.CoreProgram.pcUpper

def prefixCost (P : Parameters) : ℕ :=
  8800*(P.certificate.M+1)+30300*(P.certificate.Q+1)*(P.certificate.M+1)^2+2535

/-- Exactly the actual009 resources, retained on its SAME fixed-program
trace. Endpoint/calibration counts are deliberately not invented here. -/
structure PrefixResult (P : Parameters) (fee : ℚ) where
  trace : List State
  after : State
  head : trace.head?=some initial
  last : trace.getLast?=some after
  chain : trace.IsChain (fun first later=>step PDCompute.CoreProgram.program (preparedInput P fee) first=some later)
  timeBound : time PDCompute.CoreProgram.program trace≤prefixCost P
  pc : after.pc=PDCompute.CoreProgram.initializationPC
  ready : Ready P fee after
  calibration : HeapList after (PDLower.CalibrationCompute.resultBase (99+2*P.certificate.M) P.certificate.M)
    (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList)
  output : after.output=encodeList encodeEndpoint P.endpointCache.toList++
    encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList
  space : peakCells trace≤150*(P.certificate.M+1)
  safe : ∀ state∈trace,RootD27.Bits.SafeBits state (PDCompute.CoreGlobalBudget.budget P fee PDCompute.CoreProgram.pcUpper)
  scope : ∀ state∈trace,state.pc≤PDCompute.CoreProgram.initializationPC
  proper : ∀ state∈trace.dropLast,state.pc<PDCompute.CoreProgram.initializationPC
  requests : actualSolveRequests PDCompute.CoreProgram.labels trace=[]
  count : PaperProofs.Paid.Computation.entryCount PDCompute.CoreProgram.labels.solveEntry trace=0
  refinement : SolverCallRefinement PDCompute.CoreProgram.program PDCompute.CoreProgram.labels P fee 40000 trace

theorem initialization_alias : PDCompute.CoreProgram.initializationPC=PDCompute.CorePrelude.bodyStart := by
  unfold PDCompute.CoreProgram.initializationPC
  rfl

theorem labels_alias : PDCompute.CoreProgram.labels=
    PDCompute.CorePrelude.routineLabels PDCompute.CoreProgram.solveEntry PDCompute.CoreProgram.solveReturn := by
  unfold PDCompute.CoreProgram.labels
  rfl

theorem prefix_actual (P : Parameters) (fee : ℚ) : Nonempty (PrefixResult P fee) := by
  have outside : PDCompute.CorePrelude.bodyStart<PDCompute.CoreProgram.solveEntry := by
    have bound:=PDCompute.CoreProgram.static_bounds
    rw [←initialization_alias]
    omega
  obtain ⟨trace,after,head,last,chain,cost,pc,ready,calibration,output,space,safe,scope,proper,requests,count,refinement⟩:=
    PDCompute.CorePrelude.actual_prefix_resources PDCompute.CoreProgram.suffix.toArray P fee
      PDCompute.CoreProgram.pcUpper PDCompute.CoreProgram.solveEntry PDCompute.CoreProgram.solveReturn outside
  rw [←fixed_program] at chain cost refinement
  rw [←labels_alias] at requests refinement
  rw [←initialization_alias] at pc scope proper
  refine ⟨⟨trace,after,head,last,chain,cost,pc,ready,calibration,output,space,safe,scope,proper,requests,?_,refinement⟩⟩
  simpa only [PDCompute.CoreProgram.fixed_labels.1] using count

end PDCompute.CoreRun
