module

public import PaperProofs.Common.HealthyValue
public import PaperProofs.Statistics.Coefficient

/-! The unchanged ordered coefficient and independent rank on the actual
renumbered fresh suffix. These are structural identities, not price laws. -/

@[expose] public section

namespace PaperProofs.Common

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

theorem StatisticalInput.freshSuffix_weightedSchedule (input : StatisticalInput I) (next : ℕ) :
    (input.freshSuffix next).weightedSchedule = input.weightedSchedule.drop next := by
  cases next with
  | zero => rfl
  | succ next =>
    change (List.ofFn (fun stage : Fin (I.compatibility.drop (next + 1)).length =>
      ((I.compatibility.drop (next + 1)).get stage,
        (input.experiment (I.freshStageLift (next + 1) stage)).coefficient))) =
          input.weightedSchedule.drop (next + 1)
    apply List.ext_getElem
    · simp only [StatisticalInput.weightedSchedule, List.length_ofFn, List.length_drop]
    · intro index hleft hright
      simp only [StatisticalInput.weightedSchedule, List.getElem_drop, List.getElem_ofFn,
        List.get_eq_getElem, Instance.freshStageLift, Instance.eligible]

theorem Instance.compatibility_head_freshSuffix (first : I.Stage) (hfirst : first.val = 0) :
    I.compatibility = I.eligible first :: (I.freshSuffix 1).compatibility := by
  have hn : I.compatibility ≠ [] := by
    intro he
    have ht := first.isLt
    change first.val < I.compatibility.length at ht
    have hz : I.compatibility.length = 0 := by simp only [he, List.length_nil]
    omega
  have hcons := List.cons_head_tail hn
  change I.compatibility = I.compatibility[first.val] :: I.compatibility.drop 1
  simp only [hfirst]
  have htail : I.compatibility.tail = I.compatibility.drop 1 := by cases I.compatibility <;> rfl
  simpa only [List.head_eq_getElem, htail] using hcons.symm

theorem StatisticalInput.weightedSchedule_head_freshSuffix (input : StatisticalInput I)
    (first : I.Stage) (hfirst : first.val = 0) :
    input.weightedSchedule = (I.eligible first, (input.experiment first).coefficient) ::
      (input.freshSuffix 1).weightedSchedule := by
  rw [input.freshSuffix_weightedSchedule]
  apply List.ext_getElem
  · simp only [StatisticalInput.weightedSchedule, List.length_ofFn, List.length_cons, List.length_drop]
    have hn := first.isLt
    change first.val < I.stageCount at hn
    omega
  · intro index hleft hright
    cases index with
    | zero =>
      simp only [StatisticalInput.weightedSchedule, List.getElem_ofFn, List.getElem_cons_zero]
      have he : (⟨0, by simpa only [StatisticalInput.weightedSchedule, List.length_ofFn] using hleft⟩ : I.Stage) = first := Fin.ext hfirst.symm
      rw [he]
    | succ index =>
      simp only [List.getElem_cons_succ, List.getElem_drop]
      congr 1
      omega

theorem StatisticalInput.orderedCoefficient_head_freshSuffix (input : StatisticalInput I)
    (first : I.Stage) (hfirst : first.val = 0) (available : Finset I.Tool)
    (hfinite : errorRank I.compatibility available ≠ ⊤) :
    input.orderedCoefficient available =
      (if errorRank (I.freshSuffix 1).compatibility available = errorRank I.compatibility available
        then (input.freshSuffix 1).orderedCoefficient available else 0) +
      (if badChildRank (I.eligible first) (I.freshSuffix 1).compatibility available + 1 =
          errorRank I.compatibility available then (input.experiment first).coefficient else 0) := by
  let later : WeightedSchedule I.Tool := (input.freshSuffix 1).weightedSchedule
  let tail : List (Finset I.Tool) := (I.freshSuffix 1).compatibility
  change Statistics.orderedCoefficient input.weightedSchedule available =
    (if errorRank tail available = errorRank I.compatibility available then
      Statistics.orderedCoefficient later available else 0) +
    (if badChildRank (I.eligible first) tail available + 1 = errorRank I.compatibility available then
      (input.experiment first).coefficient else 0)
  have hweights : input.weightedSchedule = (I.eligible first, (input.experiment first).coefficient) :: later :=
    input.weightedSchedule_head_freshSuffix first hfirst
  have helig : eligibilitySchedule later = tail := (input.freshSuffix 1).weightedSchedule_eligibility
  have hcompat : I.eligible first :: tail = I.compatibility := (Instance.compatibility_head_freshSuffix first hfirst).symm
  rw [hweights]
  simp only [Statistics.orderedCoefficient, helig, hcompat, hfinite, ite_false]

theorem Instance.errorRank_head_freshSuffix (first : I.Stage) (hfirst : first.val = 0)
    (available : Finset I.Tool) :
    errorRank I.compatibility available = min (errorRank (I.freshSuffix 1).compatibility available)
      (1 + badChildRank (I.eligible first) (I.freshSuffix 1).compatibility available) := by
  conv_lhs => rw [Instance.compatibility_head_freshSuffix first hfirst]
  exact errorRank_cons _ _ _

end PaperProofs.Common
