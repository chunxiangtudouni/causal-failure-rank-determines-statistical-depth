module

public import PaperProofs.Retained.PRet_NestedComparison_074

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetNestedChildPolicy095

open Common Common.Native MeasureTheory PRetAmbientComparator073 PRetNestedComparison074
open scoped ENNReal

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- A selected ORIGINAL near-optimal child is the ACTUAL nested fresh
continuation after dependent input equality, not an assumed value identity. -/
noncomputable def nestedPolicy (input : StatisticalInput I) (first next : ℕ)
    (source : Policy (input.freshSuffix (first + next)) (freshContract (I.freshSuffix (first + next))) .uncapped
      (zeroNormalAccounting (I.freshSuffix (first + next))) Seed) :
    Policy ((input.freshSuffix first).freshSuffix next) (freshContract ((I.freshSuffix first).freshSuffix next)) .uncapped
      (zeroNormalAccounting ((I.freshSuffix first).freshSuffix next)) Seed :=
  castPolicy (I.freshSuffix_add first next).symm _ _ (input.freshSuffix_add_heq first next).symm source

theorem nestedPolicy_objective_eq (input : StatisticalInput I) (first next : ℕ) (old : Finset I.Stage)
    (source : Policy (input.freshSuffix (first + next)) (freshContract (I.freshSuffix (first + next))) .uncapped
      (zeroNormalAccounting (I.freshSuffix (first + next))) Seed)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    jointObjective ((input.freshSuffix first).freshSuffix next)
      (fun stage => I.freshStageLift first ((I.freshSuffix first).freshStageLift next stage)) old
      (nestedPolicy input first next source).rule ν penalty =
        freshObjective input (first + next) old source.rule ν penalty := by
  rw [freshObjective_eq_jointObjective]
  exact jointObjective_cast (I.freshSuffix_add first next).symm
    (input.freshSuffix (first + next)) ((input.freshSuffix first).freshSuffix next)
    (input.freshSuffix_add_heq first next).symm _ _ (nestedEmbedding_heq I first next).symm old source ν penalty

end PaperProofs.Retained.PRetNestedChildPolicy095
