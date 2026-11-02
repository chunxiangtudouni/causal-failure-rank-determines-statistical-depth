module

public import PaperProofs.Common.HealthyValue
public import Mathlib.Logic.Function.Basic

/-!
Exact composition of the original fresh-suffix data and independent native
policy infima. No recurrence, equal-value premise, alternate value, extra
tool, or controller-performance assumption is introduced. Whole binary
experiments and actual correction fees are transported by the same stage
lift, so priors, channels and observation prices are retained together.
-/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Common

variable {I : Instance}

theorem Instance.freshSuffix_add (I : Instance) (first next : ℕ) :
    (I.freshSuffix first).freshSuffix next = I.freshSuffix (first + next) := by
  cases I
  simp only [Instance.freshSuffix, List.drop_drop]

private theorem fin_val_eq_of_heq {m n : ℕ} (heq : m = n) (left : Fin m) (right : Fin n)
    (h : HEq left right) : left.val = right.val := by
  cases heq
  exact congrArg Fin.val (eq_of_heq h)

theorem Instance.freshStageLift_add (I : Instance) (first next : ℕ)
    (left : ((I.freshSuffix first).freshSuffix next).Stage)
    (right : (I.freshSuffix (first + next)).Stage) (hval : left.val = right.val) :
    I.freshStageLift first ((I.freshSuffix first).freshStageLift next left) =
      I.freshStageLift (first + next) right := by
  apply Fin.ext
  simp only [Instance.freshStageLift]
  omega

theorem StatisticalInput.freshSuffix_correctionFee (input : StatisticalInput I)
    (first : ℕ) (stage : (I.freshSuffix first).Stage) (tool : I.Tool) :
    (input.freshSuffix first).correctionFee stage tool = input.correctionFee (I.freshStageLift first stage) tool := by
  cases first with
  | zero =>
    have he : I.freshStageLift 0 stage = stage := by apply Fin.ext; simp only [Instance.freshStageLift, Nat.zero_add]
    exact congrArg (fun current : I.Stage => input.correctionFee current tool) he.symm
  | succ first => rfl

theorem StatisticalInput.freshSuffix_add_experiment (input : StatisticalInput I) (first next : ℕ)
    (left : ((I.freshSuffix first).freshSuffix next).Stage)
    (right : (I.freshSuffix (first + next)).Stage) (hval : left.val = right.val) :
    ((input.freshSuffix first).freshSuffix next).experiment left =
      (input.freshSuffix (first + next)).experiment right := by
  rw [StatisticalInput.freshSuffix_experiment, StatisticalInput.freshSuffix_experiment,
    StatisticalInput.freshSuffix_experiment]
  exact congrArg input.experiment (I.freshStageLift_add first next left right hval)

theorem StatisticalInput.freshSuffix_add_correctionFee (input : StatisticalInput I) (first next : ℕ)
    (left : ((I.freshSuffix first).freshSuffix next).Stage)
    (right : (I.freshSuffix (first + next)).Stage) (hval : left.val = right.val) (tool : I.Tool) :
    ((input.freshSuffix first).freshSuffix next).correctionFee left tool =
      (input.freshSuffix (first + next)).correctionFee right tool := by
  calc
    _ = (input.freshSuffix first).correctionFee ((I.freshSuffix first).freshStageLift next left) tool :=
      (input.freshSuffix first).freshSuffix_correctionFee next left tool
    _ = input.correctionFee (I.freshStageLift first ((I.freshSuffix first).freshStageLift next left)) tool :=
      input.freshSuffix_correctionFee first _ tool
    _ = input.correctionFee (I.freshStageLift (first + next) right) tool :=
      congrArg (fun stage : I.Stage => input.correctionFee stage tool) (I.freshStageLift_add first next left right hval)
    _ = _ := (input.freshSuffix_correctionFee (first + next) right tool).symm

private theorem statisticalInput_heq_of_fields {J K : Instance} (hI : J = K)
    (left : StatisticalInput J) (right : StatisticalInput K)
    (hexperiment : HEq left.experiment right.experiment)
    (hcorrection : HEq left.correctionFee right.correctionFee) : HEq left right := by
  cases hI
  cases left with
  | mk lexp lfee lnonneg =>
    cases right with
    | mk rexp rfee rnonneg =>
      have he : lexp = rexp := eq_of_heq hexperiment
      cases he
      have hf : lfee = rfee := eq_of_heq hcorrection
      cases hf
      rfl

/-- Actual dependent input equality, including the proof fields by proof
irrelevance. This is established from stage lifts, not assumed as a value
identity or an operational oracle. -/
theorem StatisticalInput.freshSuffix_add_heq (input : StatisticalInput I) (first next : ℕ) :
    HEq ((input.freshSuffix first).freshSuffix next) (input.freshSuffix (first + next)) := by
  have hI := I.freshSuffix_add first next
  have hStage : ((I.freshSuffix first).freshSuffix next).Stage = (I.freshSuffix (first + next)).Stage :=
    congrArg (fun J : Instance => J.Stage) hI
  have hLength : ((I.freshSuffix first).freshSuffix next).compatibility.length =
      (I.freshSuffix (first + next)).compatibility.length :=
    congrArg (fun J : Instance => J.compatibility.length) hI
  apply statisticalInput_heq_of_fields hI
  · apply Function.hfunext hStage
    intro left right h
    exact heq_of_eq (input.freshSuffix_add_experiment first next left right (fin_val_eq_of_heq hLength left right h))
  · apply Function.hfunext hStage
    intro left right h
    apply heq_of_eq
    funext tool
    exact input.freshSuffix_add_correctionFee first next left right (fin_val_eq_of_heq hLength left right h) tool

theorem StatisticalInput.freshSuffix_add_cast (input : StatisticalInput I) (first next : ℕ) :
    ((I.freshSuffix_add first next) ▸ (input.freshSuffix first).freshSuffix next) = input.freshSuffix (first + next) := by
  have hh := input.freshSuffix_add_heq first next
  exact eq_of_heq ((eqRec_heq _ _).trans hh)

private theorem canonicalPenalty_congr {J K : Instance} (hI : J = K)
    (left : StatisticalInput J) (right : StatisticalInput K) (hinput : HEq left right)
    (R : Finset J.Tool) (S : Finset K.Tool) (hR : HEq R S) (penalty : ℝ≥0∞) :
    Native.availablePenaltyValue left (currentRelaxedContract J) (zeroNormalAccounting J) R penalty =
      Native.availablePenaltyValue right (currentRelaxedContract K) (zeroNormalAccounting K) S penalty := by
  cases hI
  have hi : left = right := eq_of_heq hinput
  subst right
  have hr : R = S := eq_of_heq hR
  subst S
  rfl

/-- Exact equality of the ORIGINAL policy infima, with the same remaining
tool set. No equality of values or Bellman property is a premise. -/
theorem StatisticalInput.healthyPenalty_freshSuffix_add (input : StatisticalInput I) (first next : ℕ)
    (R : Finset I.Tool) (penalty : ℝ≥0∞) :
    (input.freshSuffix first).healthyPenalty next R penalty = input.healthyPenalty (first + next) R penalty := by
  exact canonicalPenalty_congr (I.freshSuffix_add first next) _ _ (input.freshSuffix_add_heq first next) R R (HEq.refl R) penalty

theorem StatisticalInput.healthyPenaltyReal_freshSuffix_add (input : StatisticalInput I) (first next : ℕ)
    (R : Finset I.Tool) (price : ℝ) :
    (input.freshSuffix first).healthyPenaltyReal next R price = input.healthyPenaltyReal (first + next) R price :=
  congrArg ENNReal.toReal (input.healthyPenalty_freshSuffix_add first next R (ENNReal.ofReal price))

theorem StatisticalInput.goodPenaltyReal_freshSuffix (input : StatisticalInput I) (first : ℕ)
    (stage : (I.freshSuffix first).Stage) (R : Finset I.Tool) (price : ℝ) :
    (input.freshSuffix first).goodPenaltyReal stage R price =
      input.goodPenaltyReal (I.freshStageLift first stage) R price := by
  unfold StatisticalInput.goodPenaltyReal
  rw [StatisticalInput.healthyPenaltyReal_freshSuffix_add]
  simp only [Instance.freshStageLift, Nat.add_assoc]

theorem StatisticalInput.badPenaltyReal_freshSuffix (input : StatisticalInput I) (first : ℕ)
    (stage : (I.freshSuffix first).Stage) (R : Finset I.Tool) (price : ℝ) :
    (input.freshSuffix first).badPenaltyReal stage R price =
      input.badPenaltyReal (I.freshStageLift first stage) R price := by
  classical
  have hindex : first + (stage.val + 1) = (I.freshStageLift first stage).val + 1 := by
    simp only [Instance.freshStageLift, Nat.add_assoc]
  have hvalue : (fun tool : I.Tool =>
      (input.freshSuffix first).healthyPenaltyReal (stage.val + 1) (R.erase tool) price) =
      (fun tool : I.Tool => input.healthyPenaltyReal
        ((I.freshStageLift first stage).val + 1) (R.erase tool) price) := by
    funext tool
    simpa only [hindex] using input.healthyPenaltyReal_freshSuffix_add first (stage.val + 1) (R.erase tool) price
  simp only [StatisticalInput.badPenaltyReal, Instance.freshSuffix_eligible]
  change (if h : (I.eligible (I.freshStageLift first stage) ∩ R).Nonempty then
      (I.eligible (I.freshStageLift first stage) ∩ R).inf' h
        (fun tool : I.Tool => (input.freshSuffix first).healthyPenaltyReal
          (stage.val + 1) (R.erase tool) price) else price) = _
  rw [hvalue]

/-- The actual zero-indexed head of the suffix starting at a given stage. -/
def Instance.freshHead (I : Instance) (stage : I.Stage) : (I.freshSuffix stage.val).Stage :=
  ⟨0, by
    have hs := stage.isLt
    change stage.val < I.compatibility.length at hs
    change 0 < (I.compatibility.drop stage.val).length
    rw [List.length_drop]
    omega⟩

@[simp] theorem Instance.freshHead_val (I : Instance) (stage : I.Stage) : (I.freshHead stage).val = 0 := rfl

@[simp] theorem Instance.freshStageLift_freshHead (I : Instance) (stage : I.Stage) :
    I.freshStageLift stage.val (I.freshHead stage) = stage := by
  apply Fin.ext
  simp only [Instance.freshStageLift, Instance.freshHead, Nat.add_zero]

theorem StatisticalInput.freshHead_recursion_iff (input : StatisticalInput I)
    (stage : I.Stage) (R : Finset I.Tool) (price : ℝ) :
    ((input.freshSuffix stage.val).healthyPenaltyReal 0 R price =
      min price ((input.freshSuffix stage.val).goodPenaltyReal (I.freshHead stage) R price +
        ((input.freshSuffix stage.val).experiment (I.freshHead stage)).localValueReal
          ((input.freshSuffix stage.val).badPenaltyReal (I.freshHead stage) R price -
           (input.freshSuffix stage.val).goodPenaltyReal (I.freshHead stage) R price))) ↔
    (input.healthyPenaltyReal stage.val R price =
      min price (input.goodPenaltyReal stage R price + (input.experiment stage).localValueReal
        (input.badPenaltyReal stage R price - input.goodPenaltyReal stage R price))) := by
  simp only [StatisticalInput.healthyPenaltyReal_freshSuffix_add, Nat.add_zero,
    StatisticalInput.goodPenaltyReal_freshSuffix, StatisticalInput.badPenaltyReal_freshSuffix,
    StatisticalInput.freshSuffix_experiment, Instance.freshStageLift_freshHead]

theorem StatisticalInput.freshHead_lower_iff (input : StatisticalInput I)
    (stage : I.Stage) (R : Finset I.Tool) (price : ℝ) :
    (min price ((input.freshSuffix stage.val).goodPenaltyReal (I.freshHead stage) R price +
        ((input.freshSuffix stage.val).experiment (I.freshHead stage)).localValueReal
          ((input.freshSuffix stage.val).badPenaltyReal (I.freshHead stage) R price -
           (input.freshSuffix stage.val).goodPenaltyReal (I.freshHead stage) R price)) ≤
      (input.freshSuffix stage.val).healthyPenaltyReal 0 R price) ↔
    (min price (input.goodPenaltyReal stage R price + (input.experiment stage).localValueReal
      (input.badPenaltyReal stage R price - input.goodPenaltyReal stage R price)) ≤
      input.healthyPenaltyReal stage.val R price) := by
  simp only [StatisticalInput.healthyPenaltyReal_freshSuffix_add, Nat.add_zero,
    StatisticalInput.goodPenaltyReal_freshSuffix, StatisticalInput.badPenaltyReal_freshSuffix,
    StatisticalInput.freshSuffix_experiment, Instance.freshStageLift_freshHead]

theorem StatisticalInput.freshHead_upper_iff (input : StatisticalInput I)
    (stage : I.Stage) (R : Finset I.Tool) (price : ℝ) :
    ((input.freshSuffix stage.val).healthyPenaltyReal 0 R price ≤
      min price ((input.freshSuffix stage.val).goodPenaltyReal (I.freshHead stage) R price +
        ((input.freshSuffix stage.val).experiment (I.freshHead stage)).localValueReal
          ((input.freshSuffix stage.val).badPenaltyReal (I.freshHead stage) R price -
           (input.freshSuffix stage.val).goodPenaltyReal (I.freshHead stage) R price))) ↔
    (input.healthyPenaltyReal stage.val R price ≤
      min price (input.goodPenaltyReal stage R price + (input.experiment stage).localValueReal
        (input.badPenaltyReal stage R price - input.goodPenaltyReal stage R price))) := by
  simp only [StatisticalInput.healthyPenaltyReal_freshSuffix_add, Nat.add_zero,
    StatisticalInput.goodPenaltyReal_freshSuffix, StatisticalInput.badPenaltyReal_freshSuffix,
    StatisticalInput.freshSuffix_experiment, Instance.freshStageLift_freshHead]

/-- Rewriting every genuinely fresh head formula gives exactly the existing
CurrentPenaltyRecursion statement, without changing the independent value. -/
theorem StatisticalInput.currentPenaltyRecursion_iff_freshHeads (input : StatisticalInput I) :
    input.CurrentPenaltyRecursion ↔
      ∀ (stage : I.Stage) (R : Finset I.Tool) (price : ℝ), 0 < price →
      (input.freshSuffix stage.val).healthyPenaltyReal 0 R price =
        min price ((input.freshSuffix stage.val).goodPenaltyReal (I.freshHead stage) R price +
          ((input.freshSuffix stage.val).experiment (I.freshHead stage)).localValueReal
            ((input.freshSuffix stage.val).badPenaltyReal (I.freshHead stage) R price -
             (input.freshSuffix stage.val).goodPenaltyReal (I.freshHead stage) R price)) := by
  simp only [StatisticalInput.CurrentPenaltyRecursion, StatisticalInput.freshHead_recursion_iff]

end PaperProofs.Common
