module

public import PaperProofs.Retained.PRet_AmbientComparator_073

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetNestedComparison074

open Common Common.Native MeasureTheory PRetAmbientComparator073
open scoped ENNReal

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

theorem stage_val_eq_of_heq {J K : Instance} (hI : J = K) (left : J.Stage) (right : K.Stage)
    (h : HEq left right) : left.val = right.val := by
  cases hI
  exact congrArg Fin.val (eq_of_heq h)

theorem nestedEmbedding_heq (I : Instance) (first next : ℕ) :
    HEq (fun stage : ((I.freshSuffix first).freshSuffix next).Stage =>
      I.freshStageLift first ((I.freshSuffix first).freshStageLift next stage))
      (I.freshStageLift (first + next)) := by
  have hI := I.freshSuffix_add first next
  apply Function.hfunext (congrArg (fun J : Instance => J.Stage) hI)
  intro left right h
  exact heq_of_eq (I.freshStageLift_add first next left right (stage_val_eq_of_heq hI left right h))

/-- The exact original independent fresh infimum compares to a nested
ACTUAL extraction policy after the proved dependent input/stage transport.
All old H remains in the ambient ORIGINAL input; no value identity with G
or physical native-success assumption is used. -/
theorem freshPenalty_le_nested_extraction (input : StatisticalInput I) (first next : ℕ)
    (old : Finset I.Stage) (accounting : NormalAccounting (I.freshSuffix first))
    (source : PolicyRule (I.freshSuffix first) Seed) (hm : MeasurableRule source)
    (startup : Startup (I.freshSuffix first)) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (penalty : ℝ≥0∞) :
    freshPenalty input (first + next) old penalty ≤
      jointObjective ((input.freshSuffix first).freshSuffix next)
        (fun stage => I.freshStageLift first ((I.freshSuffix first).freshStageLift next stage)) old
        (PRetFreshExtractionPolicy047.rule next accounting source startup) ν penalty := by
  let target := PRetFreshExtractionPolicy047.policy (input.freshSuffix first) next accounting source hm startup
  let transported := castPolicy (I.freshSuffix_add first next) _ _ (input.freshSuffix_add_heq first next) target
  have h := freshPenalty_le_policy_any_seed input (first + next) old penalty ν transported
  rw [freshObjective_eq_jointObjective] at h
  have heq := jointObjective_cast (I.freshSuffix_add first next)
    ((input.freshSuffix first).freshSuffix next) (input.freshSuffix (first + next))
    (input.freshSuffix_add_heq first next) _ _ (nestedEmbedding_heq I first next) old target ν penalty
  change jointObjective (input.freshSuffix (first + next)) (I.freshStageLift (first + next)) old
    transported.rule ν penalty = _ at heq
  rw [heq] at h
  exact h

end PaperProofs.Retained.PRetNestedComparison074
