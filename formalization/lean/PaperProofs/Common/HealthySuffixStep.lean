module

public import PaperProofs.Common.FreshCoefficient
public import PaperProofs.Common.PenaltyAsymptotics

/-!
One-step rank and coefficient identities at the original suffix index.
These adapters keep a single fixed input throughout the B11/B12 backward
induction; they do not assume any statistical asymptotic or redefine G.
-/

@[expose] public section

namespace PaperProofs.Common

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

theorem Instance.compatibility_suffix_cons (I : Instance) (stage : I.Stage) :
    I.compatibility.drop stage.val = I.eligible stage :: I.compatibility.drop (stage.val + 1) :=
  List.drop_eq_getElem_cons stage.isLt

theorem Instance.errorRank_suffix_step (I : Instance) (stage : I.Stage)
    (available : Finset I.Tool) :
    errorRank (I.compatibility.drop stage.val) available =
      min (errorRank (I.compatibility.drop (stage.val + 1)) available)
        (1 + badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available) := by
  rw [I.compatibility_suffix_cons stage]
  exact errorRank_cons _ _ _

theorem StatisticalInput.weightedSchedule_suffix_cons (input : StatisticalInput I)
    (stage : I.Stage) :
    (input.freshSuffix stage.val).weightedSchedule =
      (I.eligible stage, (input.experiment stage).coefficient) ::
        (input.freshSuffix (stage.val + 1)).weightedSchedule := by
  rw [input.freshSuffix_weightedSchedule, input.freshSuffix_weightedSchedule]
  have hlt : stage.val < input.weightedSchedule.length := by
    simpa only [StatisticalInput.weightedSchedule, List.length_ofFn] using stage.isLt
  rw [List.drop_eq_getElem_cons hlt]
  simp only [StatisticalInput.weightedSchedule, List.getElem_ofFn]
  cases stage
  rfl

theorem StatisticalInput.suffixCoefficient_step (input : StatisticalInput I)
    (stage : I.Stage) (available : Finset I.Tool)
    (hfinite : errorRank (I.compatibility.drop stage.val) available ≠ ⊤) :
    input.suffixCoefficient stage.val available =
      (if errorRank (I.compatibility.drop (stage.val + 1)) available =
          errorRank (I.compatibility.drop stage.val) available then
        input.suffixCoefficient (stage.val + 1) available else 0) +
      (if badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available + 1 =
          errorRank (I.compatibility.drop stage.val) available then
        (input.experiment stage).coefficient else 0) := by
  let current : WeightedSchedule I.Tool := (input.freshSuffix stage.val).weightedSchedule
  let later : WeightedSchedule I.Tool := (input.freshSuffix (stage.val + 1)).weightedSchedule
  let tail : List (Finset I.Tool) := I.compatibility.drop (stage.val + 1)
  change Statistics.orderedCoefficient current available =
    (if errorRank tail available = errorRank (I.compatibility.drop stage.val) available then
      Statistics.orderedCoefficient later available else 0) +
    (if badChildRank (I.eligible stage) tail available + 1 =
        errorRank (I.compatibility.drop stage.val) available then
      (input.experiment stage).coefficient else 0)
  have hweights : current = (I.eligible stage, (input.experiment stage).coefficient) :: later :=
    input.weightedSchedule_suffix_cons stage
  have helig : eligibilitySchedule later = tail :=
    (input.freshSuffix (stage.val + 1)).weightedSchedule_eligibility
  have hcompat : I.eligible stage :: tail = I.compatibility.drop stage.val :=
    (I.compatibility_suffix_cons stage).symm
  rw [hweights]
  simp only [Statistics.orderedCoefficient, helig, hcompat, hfinite, ite_false]

theorem StatisticalInput.suffixCoefficient_pos (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool)
    (hfinite : errorRank (I.compatibility.drop next) available ≠ ⊤) :
    0 < input.suffixCoefficient next available :=
  (input.freshSuffix next).orderedCoefficient_pos available hfinite

theorem StatisticalInput.suffixCoefficient_zero_of_infiniteRank (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool)
    (htop : errorRank (I.compatibility.drop next) available = ⊤) :
    input.suffixCoefficient next available = 0 := by
  unfold StatisticalInput.suffixCoefficient StatisticalInput.orderedCoefficient
  apply Statistics.orderedCoefficient_of_infiniteRank
  rw [(input.freshSuffix next).weightedSchedule_eligibility]
  exact htop

theorem Instance.badChildRank_suffix_ne_top (I : Instance) (stage : I.Stage)
    (available : Finset I.Tool)
    (hfinite : errorRank (I.compatibility.drop stage.val) available ≠ ⊤) :
    badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available ≠ ⊤ := by
  intro hbad
  have hgood : errorRank (I.compatibility.drop (stage.val + 1)) available = ⊤ :=
    top_le_iff.mp (hbad ▸ badChildRank_le_goodRank (I.eligible stage)
      (I.compatibility.drop (stage.val + 1)) available)
  apply hfinite
  rw [I.errorRank_suffix_step stage available, hgood, hbad, add_top, min_self]

end PaperProofs.Common
