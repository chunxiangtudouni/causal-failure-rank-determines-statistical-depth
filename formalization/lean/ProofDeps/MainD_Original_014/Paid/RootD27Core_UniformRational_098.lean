module

public import Paid.RootD27Core_CountedPrefix_097
public import Paid.PDCompute_CoreRun_Actual_004
public import Paid.PDCompute_RationalAuxiliary_CoreAssembly_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.CoreRun PDCompute.RationalAuxiliary

attribute [local irreducible] PDCompute.CoreProgram.program PDCompute.CoreProgram.labels
  PDCompute.CoreProgram.pcUpper

/-- All ORIGINAL fourth-field requirements, on one actual run of one
fixed program. The two original phase counts are produced internally. -/
theorem original_core_field :
    CoreField PDCompute.CoreProgram.program PDCompute.CoreProgram.labels
      300000 512 fixedBitsConstant := by
  intro P fee _nonnegative
  obtain ⟨front,endpoints,calibration⟩:=counted_prefix_actual P fee
  obtain ⟨trace,final,run,decoded,encoded,cost,space,bits,requests,count,countBound,
      endpointCount,calibrationCount,calls⟩:=counted_prefix_run P fee front endpoints calibration
  exact ⟨trace,final,run,decoded,encoded,cost,space,bits,requests,count,countBound,
    endpointCount,calibrationCount,original_call_constant_mono calls (by omega)⟩

/-- The complete original uniform rational implementation claim, with
programs and all positive common constants chosen before P and fee. -/
theorem uniform_rational_implementation_claims : UniformRationalImplementationClaims :=
  original_uniform_of_core PDCompute.CoreProgram.program PDCompute.CoreProgram.labels
    300000 512 fixedBitsConstant original_core_field

end RootD27.Core
