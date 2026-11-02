module

public import Paid.RootD27Core_SelectedMetadata_069
public import Paid.PDCompute_SolverCoreScale_218

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver

namespace PDLower.CoreRuntimeNumeric

/-- Both real retained buffers, all source/copy endpoints and every
setup arithmetic value. This depends on raw/control dimensions, not on
the incoming dirty state or a chosen caller resource witness. -/
def runtimeAddressLimit (P : Parameters) : ℕ :=
  (99+2*P.certificate.M)+78*PDCompute.Solver.entryCount P.certificate.stages P.tools

theorem address_limit_arithmetic (M N K : ℕ) :
    1+natBits ((99+2*M)+78*((N+1)*(K+1)))≤20+natBits M+natBits N+natBits K := by
  have base := natBits_add_le 99 (2*M)
  have twice := natBits_mul_le 2 M
  have entries := natBits_mul_le (N+1) (K+1)
  have rows := natBits_add_le N 1
  have columns := natBits_add_le K 1
  have buffers := natBits_mul_le 78 ((N+1)*(K+1))
  have combined := natBits_add_le (99+2*M) (78*((N+1)*(K+1)))
  have constants : natBits 99=7 ∧ natBits 2=2 ∧ natBits 78=7 ∧ natBits 1=1 := by decide
  omega

theorem runtime_address_room_le_core (P : Parameters) (fee : ℚ) :
    (Cell.natural (runtimeAddressLimit P)).bits≤32*coreOperandBound P fee := by
  have dimensions : natBits P.certificate.stages≤P.certificate.stages+1 :=
    Nat.add_le_add_right (Nat.log2_le_self _) 1
  have sourceDimensions : natBits P.certificate.stages+natBits P.tools≤rawSize P fee := by
    unfold rawSize
    omega
  have coreTerms : rawSize P fee+natBits P.certificate.M≤coreOperandBound P fee := by
    unfold coreOperandBound
    omega
  have positive : 1≤coreOperandBound P fee := by unfold coreOperandBound;omega
  have calculated := address_limit_arithmetic P.certificate.M P.certificate.stages P.tools
  change 1+natBits ((99+2*P.certificate.M)+78*((P.certificate.stages+1)*(P.tools+1)))≤_
  omega

theorem runtime_original_count_bound (P : Parameters) (fee penalty : ℚ) :
    (RootD27.Core.originalSolveEncoding P fee penalty).length≤8*PDCompute.Solver.entryCount P.certificate.stages P.tools := by
  exact (RootD27.Core.original_table_capacity P fee penalty P.certificate.stages P.tools).trans
    (RootD27.Core.retained_capacity_enough P.certificate.stages P.tools)

theorem runtime_base_le_limit (P : Parameters) : 99+2*P.certificate.M≤runtimeAddressLimit P := by
  unfold runtimeAddressLimit
  omega

theorem runtime_source_end_le_limit (P : Parameters) (fee penalty : ℚ) :
    resultBase (99+2*P.certificate.M) P.certificate.stages P.tools+(RootD27.Core.originalSolveEncoding P fee penalty).length≤
      runtimeAddressLimit P := by
  have beforeBuffer := RootD27.Core.original_table_before_retained P fee penalty (99+2*P.certificate.M)
    P.certificate.stages P.tools true
  change resultBase (99+2*P.certificate.M) P.certificate.stages P.tools+(RootD27.Core.originalSolveEncoding P fee penalty).length≤
    RootD27.Core.retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools true at beforeBuffer
  change resultBase (99+2*P.certificate.M) P.certificate.stages P.tools+(RootD27.Core.originalSolveEncoding P fee penalty).length≤
    (99+2*P.certificate.M)+70*PDCompute.Solver.entryCount P.certificate.stages P.tools at beforeBuffer
  unfold runtimeAddressLimit
  omega

theorem runtime_target_end_le_limit (P : Parameters) (fee penalty : ℚ) (upper : Bool) :
    RootD27.Core.retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper+
      (RootD27.Core.originalSolveEncoding P fee penalty).length≤runtimeAddressLimit P := by
  have count := runtime_original_count_bound P fee penalty
  cases upper <;> simp only [RootD27.Core.retainedTableBase,Bool.false_eq_true,ite_false,ite_true]
  all_goals unfold runtimeAddressLimit;omega

/-- Lift only actual newly computed natural values to the GIVEN B.
All old registers/live/output remain covered by their separate carry. -/
theorem runtime_natural_room (P : Parameters) (fee : ℚ) (budget value : ℕ)
    (room : 32*coreOperandBound P fee≤budget) (bounded : value≤runtimeAddressLimit P) :
    (Cell.natural value).bits≤budget :=
  (Nat.add_le_add_left (natBits_mono bounded) 1).trans ((runtime_address_room_le_core P fee).trans room)

end PDLower.CoreRuntimeNumeric
