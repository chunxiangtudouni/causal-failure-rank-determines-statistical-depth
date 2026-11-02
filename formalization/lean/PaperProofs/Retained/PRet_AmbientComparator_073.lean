module

public import PaperProofs.Retained.PRet_FreshExtractionPolicy_047
public import PaperProofs.Common.FreshSuffixComposition

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetAmbientComparator073

open Common Common.Native MeasureTheory

open scoped ENNReal

variable {Physical Ambient : Instance} {Seed : Type*}

/-- The existing fresh success predicate exposed with its ambient stage
embedding. This is only a predicate on the same actual interpreter; it adds
neither an alternative policy class nor a Bellman-defined value. -/
def jointSuccess (input : StatisticalInput Physical) (embed : Physical.Stage → Ambient.Stage)
    (old : Finset Ambient.Stage) (rule : PolicyRule Physical Seed) (sample : Seed × input.World) : Prop :=
  ∃ n,
    let state := run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) rule sample n
    state.halted = true ∧ state.ledger.finished = true ∧ state.ledger.abandoned = false ∧
      Matchable Ambient (old ∪ (ordinaryMismatches state.ledger).image embed)

variable [MeasurableSpace Seed]

noncomputable def jointObjective (input : StatisticalInput Physical) (embed : Physical.Stage → Ambient.Stage)
    (old : Finset Ambient.Stage) (rule : PolicyRule Physical Seed) (ν : Measure Seed) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  expectedObservationBill input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) rule ν +
    penalty * input.seededWorldLaw ν {sample | ¬ jointSuccess input embed old rule sample}

omit [MeasurableSpace Seed] in
theorem freshSuccess_eq_jointSuccess (input : StatisticalInput Ambient) (first : ℕ)
    (old : Finset Ambient.Stage) (rule : PolicyRule (Ambient.freshSuffix first) Seed)
    (sample : Seed × (input.freshSuffix first).World) :
    freshSuccess input first old rule sample ↔
      jointSuccess (input.freshSuffix first) (Ambient.freshStageLift first) old rule sample := Iff.rfl

theorem freshObjective_eq_jointObjective (input : StatisticalInput Ambient) (first : ℕ)
    (old : Finset Ambient.Stage) (rule : PolicyRule (Ambient.freshSuffix first) Seed)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    freshObjective input first old rule ν penalty =
      jointObjective (input.freshSuffix first) (Ambient.freshStageLift first) old rule ν penalty := rfl

/-- Transport an ACTUAL globally legal fresh policy only along already
proved dependent input equality. No performance or source/output equality
is assumed. -/
noncomputable def castPolicy {J K : Instance} (hI : J = K)
    (left : StatisticalInput J) (right : StatisticalInput K) (hinput : HEq left right)
    (policy : Policy left (freshContract J) .uncapped (zeroNormalAccounting J) Seed) :
    Policy right (freshContract K) .uncapped (zeroNormalAccounting K) Seed := by
  cases hI
  have heq : left = right := eq_of_heq hinput
  cases heq
  exact policy

theorem jointObjective_cast {J K : Instance} (hI : J = K)
    (left : StatisticalInput J) (right : StatisticalInput K) (hinput : HEq left right)
    (embedLeft : J.Stage → Ambient.Stage) (embedRight : K.Stage → Ambient.Stage)
    (hembed : HEq embedLeft embedRight) (old : Finset Ambient.Stage)
    (policy : Policy left (freshContract J) .uncapped (zeroNormalAccounting J) Seed)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    jointObjective right embedRight old (castPolicy hI left right hinput policy).rule ν penalty =
      jointObjective left embedLeft old policy.rule ν penalty := by
  cases hI
  have hi : left = right := eq_of_heq hinput
  cases hi
  have he : embedLeft = embedRight := eq_of_heq hembed
  cases he
  rfl

end PaperProofs.Retained.PRetAmbientComparator073





