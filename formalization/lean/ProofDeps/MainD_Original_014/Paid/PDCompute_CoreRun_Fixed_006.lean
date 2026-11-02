module
public import Paid.PDCompute_CoreRun_Complete_005
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

/-- Instantiate the compiled abstract join with the ONE frozen ROM,
actual009 prefix and actual945 main. No program expression is unfolded. -/
theorem generic_actual (P : Parameters) (fee : ℚ) (front : PrefixResult P fee) :
    Nonempty (Generic.Joined PDCompute.CoreProgram.program PDCompute.CoreProgram.labels P fee
      PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.pcUpper front.trace front.after) := by
  obtain ⟨main⟩:=main_actual P fee front
  obtain ⟨joined⟩:=Generic.assemble PDCompute.CoreProgram.program PDCompute.CoreProgram.labels P fee
    PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.pcUpper front.trace front.after
    front.head front.last front.chain front.timeBound front.pc front.output front.space front.safe front.requests front.count front.refinement
    main main_end PDCompute.CoreProgram.static_bounds.1 PDCompute.CoreProgram.fixed_labels.2.2.1 PDCompute.CoreProgram.fixed_labels.2.2.2
  exact ⟨joined⟩

abbrev FixedResult (P : Parameters) (fee : ℚ) (front : PrefixResult P fee) :=
  Generic.Joined PDCompute.CoreProgram.program PDCompute.CoreProgram.labels P fee
    PDCompute.CoreProgram.initializationPC PDCompute.CoreProgram.pcUpper front.trace front.after

abbrev fixedBitsConstant : ℕ := Generic.bitFactor PDCompute.CoreProgram.pcUpper

theorem bit_factor_positive (upper : ℕ) : 0<Generic.bitFactor upper := by
  unfold Generic.bitFactor
  omega

theorem fixedBitsConstant_positive : 0<fixedBitsConstant :=
  bit_factor_positive PDCompute.CoreProgram.pcUpper

theorem from_prefix (P : Parameters) (fee : ℚ) (front : PrefixResult P fee) :
    Nonempty (FixedResult P fee front) := generic_actual P fee front

end PDCompute.CoreRun
