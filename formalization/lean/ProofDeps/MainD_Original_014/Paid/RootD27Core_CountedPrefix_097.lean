module

public import Paid.PDCompute_CoreRun_Prefix_002
public import Paid.PDCompute_CorePrelude_Complete_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDCompute.CoreRun

attribute [local irreducible] matrixCode solverCalleeCode PDLower.CalibrationCompute.kernel
  PDCompute.CorePrelude.program PDCompute.CorePrelude.bodyStart PDCompute.CorePrelude.afterCalibration
  PDCompute.CoreProgram.program PDCompute.CoreProgram.suffix PDCompute.CoreProgram.calleeCode
  PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.solveEntry PDCompute.CoreProgram.solveReturn
  PDCompute.CoreProgram.labels PDCompute.CoreProgram.pcUpper

/-- The SAME physically produced original prefix supplies both original
phase counts. No comparison with a separately chosen prefix is needed. -/
theorem counted_prefix_actual (P : Parameters) (fee : ℚ) :
    ∃ front : PrefixResult P fee,
      PaperProofs.Paid.Computation.entryCount 52 front.trace=1 ∧
      PaperProofs.Paid.Computation.entryCount 316 front.trace=1 := by
  have outside : PDCompute.CorePrelude.bodyStart<PDCompute.CoreProgram.solveEntry := by
    have bound:=PDCompute.CoreProgram.static_bounds
    rw [←initialization_alias]
    omega
  obtain ⟨trace,after,head,last,chain,cost,pc,ready,calibration,output,space,safe,scope,proper,
      requests,count,refinement,endpoints,calibrations⟩:=
    PDCompute.CorePrelude.actual_prefix_complete_minimal PDCompute.CoreProgram.suffix.toArray P fee
      PDCompute.CoreProgram.pcUpper PDCompute.CoreProgram.solveEntry PDCompute.CoreProgram.solveReturn outside
  rw [←fixed_program] at chain cost refinement
  rw [←labels_alias] at requests refinement
  rw [←initialization_alias] at pc scope proper
  have noSolver : PaperProofs.Paid.Computation.entryCount PDCompute.CoreProgram.labels.solveEntry trace=0 := by
    simpa only [PDCompute.CoreProgram.fixed_labels.1] using count
  exact ⟨⟨trace,after,head,last,chain,cost,pc,ready,calibration,output,space,safe,scope,proper,
    requests,noSolver,refinement⟩,endpoints,calibrations⟩

end RootD27.Core
