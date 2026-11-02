module
public import Paid.PDCompute_CoreRun_Fixed_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
@[expose] public section
namespace PDCompute.CoreRun
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame

attribute [local irreducible] PDCompute.CoreProgram.program PDCompute.CoreProgram.labels PDCompute.CoreProgram.pcUpper

/-- Unconditional actual fixed-core execution from original P/fee. All
fields except the two early-entry counts are already proved by actual009.
The exact prefix witness is retained for its later minimal counted proof. -/
theorem actual (P : Parameters) (fee : ℚ) :
    ∃ front : PrefixResult P fee,Nonempty (FixedResult P fee front) := by
  obtain ⟨front⟩:=prefix_actual P fee
  exact ⟨front,from_prefix P fee front⟩

/-- Pure connection of the SAME actual prefix's two counts to the SAME
whole-core run. These are INTERNAL producer fields, not new original
CoreField assumptions; the minimal actual020 discharges them in Root. -/
theorem counted_prefix_run (P : Parameters) (fee : ℚ) (front : PrefixResult P fee)
    (endpoints : entryCount 52 front.trace=1) (calibration : entryCount 316 front.trace=1) :
    ∃ trace final,Runs PDCompute.CoreProgram.program (preparedInput P fee) trace final ∧
      decodeArtifact final.output=some (buildArtifact P fee) ∧
      final.output=encodeArtifact (buildArtifact P fee) ∧
      time PDCompute.CoreProgram.program trace≤300000*sourceCoreScale P fee ∧
      peakCells trace≤512*sourceRecordSpace P ∧
      peakOperandBits trace≤fixedBitsConstant*coreOperandBound P fee ∧
      actualSolveRequests PDCompute.CoreProgram.labels trace=
        (P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2 ∧
      entryCount PDCompute.CoreProgram.labels.solveEntry trace=(actualSolveRequests PDCompute.CoreProgram.labels trace).length ∧
      entryCount PDCompute.CoreProgram.labels.solveEntry trace≤P.bisectionBudget fee+2 ∧
      entryCount PDCompute.CoreProgram.labels.endpointEntry trace=1 ∧
      entryCount PDCompute.CoreProgram.labels.calibrationEntry trace=1 ∧
      SolverCallRefinement PDCompute.CoreProgram.program PDCompute.CoreProgram.labels P fee 40000 trace := by
  obtain ⟨result⟩:=from_prefix P fee front
  exact ⟨result.trace,result.after,result.run,result.decoded,result.output,result.timeBound,result.space,result.bits,
    result.requests,result.countExact,result.countBound,result.endpointCount.trans endpoints,
    result.calibrationCount.trans calibration,result.refinement⟩

end PDCompute.CoreRun
