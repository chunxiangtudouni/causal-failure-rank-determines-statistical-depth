module

public import PaperProofs.Statistics.ReferenceBudgets
public import Mathlib.Basic.ENNReal.Real

/-!
One-stage mass bounds for the ACTUAL referenceBudgetTarget/Step updates of
frozen price-proofs.tex:187--209. The input error-mass bound is the local
SPRT conclusion; it is not added to any comparison policy or budget state.
All masses are ENNReal and may be infinite. No cost, ET or probability-space
finiteness hypothesis is needed for this algebraic transfer.
-/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Statistics

/-- A loose good-branch mass bound is sufficient. In particular good may
equal entry, as needed to avoid constructing a correct/error partition. -/
theorem weighted_two_branch_mass_le (entry good error a b p risk : ℝ≥0∞)
    (hgood : good ≤ entry) (herror : error ≤ p * entry) (hcoefficient : a + b * p ≤ risk) :
    a * good + b * error ≤ risk * entry := by
  calc
    _ ≤ a * entry + b * (p * entry) :=
      add_le_add (mul_le_mul_right hgood a) (mul_le_mul_right herror b)
    _ = (a + b * p) * entry := by ring
    _ ≤ _ := mul_le_mul_left hcoefficient entry

theorem referenceBudget_half_add (risk : ℚ) (hrisk : 0 ≤ risk) :
    ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) + ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) =
      ENNReal.ofReal (risk : ℝ) := by
  have hhalf : (0 : ℝ) ≤ ((risk / 2 : ℚ) : ℝ) := by exact_mod_cast (div_nonneg hrisk (by norm_num : (0 : ℚ) ≤ 2))
  rw [← ENNReal.ofReal_add hhalf hhalf]
  congr 1
  push_cast
  ring

theorem referenceBudget_noTool_mass (risk : ℚ) (hrisk : 0 ≤ risk) (entry good error : ℝ≥0∞)
    (hgood : good ≤ entry) (herror : error ≤ ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * entry) :
    ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * good + error ≤ ENNReal.ofReal (risk : ℝ) * entry := by
  have hcoefficient : ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) +
      1 * ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) ≤ ENNReal.ofReal (risk : ℝ) := by
    rw [one_mul, referenceBudget_half_add risk hrisk]
  simpa only [one_mul] using weighted_two_branch_mass_le entry good error
    (ENNReal.ofReal ((risk / 2 : ℚ) : ℝ)) 1 (ENNReal.ofReal ((risk / 2 : ℚ) : ℝ))
    (ENNReal.ofReal (risk : ℝ)) hgood herror hcoefficient

/-- The finite-bad coefficient uses the original p_j and original clipped
bad budget. Its <=r/2 bound is proved in ControllerThresholds. -/
theorem referenceBudget_finiteBad_coefficient (risk : ℚ) (hvalid : ReferenceBudgetValid risk) (depth : ℕ+) :
    ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) +
      ENNReal.ofReal ((controllerBadRisk risk (controllerTarget risk depth.val) : ℚ) : ℝ) *
        ENNReal.ofReal ((controllerTarget risk depth.val : ℚ) : ℝ) ≤ ENNReal.ofReal (risk : ℝ) := by
  let target := controllerTarget risk depth.val
  let child := controllerBadRisk risk target
  have htarget : 0 < target := controllerTarget_pos risk depth.val
  have hchild : 0 < child := controllerBadRisk_positive risk target hvalid.1 hvalid.2 htarget
    (controllerTarget_le_quarter risk depth.val)
  have hproduct : ENNReal.ofReal (child : ℝ) * ENNReal.ofReal (target : ℝ) ≤
      ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) := by
    calc
      _ = ENNReal.ofReal ((target * child : ℚ) : ℝ) := by
        rw [← ENNReal.ofReal_mul (by exact_mod_cast hchild.le)]
        congr 1
        push_cast
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by exact_mod_cast controllerBadRisk_budget risk target htarget)
  exact (add_le_add_right hproduct (ENNReal.ofReal ((risk / 2 : ℚ) : ℝ))).trans_eq
    (referenceBudget_half_add risk hvalid.1.le)

theorem referenceBudget_finiteBad_mass (risk : ℚ) (hvalid : ReferenceBudgetValid risk) (depth : ℕ+)
    (entry good error : ℝ≥0∞) (hgood : good ≤ entry)
    (herror : error ≤ ENNReal.ofReal ((controllerTarget risk depth.val : ℚ) : ℝ) * entry) :
    ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * good +
      ENNReal.ofReal ((controllerBadRisk risk (controllerTarget risk depth.val) : ℚ) : ℝ) * error ≤
        ENNReal.ofReal (risk : ℝ) * entry :=
  weighted_two_branch_mass_le entry good error
    (ENNReal.ofReal ((risk / 2 : ℚ) : ℝ))
    (ENNReal.ofReal ((controllerBadRisk risk (controllerTarget risk depth.val) : ℚ) : ℝ))
    (ENNReal.ofReal ((controllerTarget risk depth.val : ℚ) : ℝ)) (ENNReal.ofReal (risk : ℝ))
    hgood herror (referenceBudget_finiteBad_coefficient risk hvalid depth)

theorem referenceBudget_noTool_entry_mass (risk : ℚ) (hrisk : 0 ≤ risk) (entry error : ℝ≥0∞)
    (herror : error ≤ ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * entry) :
    ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * entry + error ≤ ENNReal.ofReal (risk : ℝ) * entry :=
  referenceBudget_noTool_mass risk hrisk entry entry error le_rfl herror

theorem referenceBudget_finiteBad_entry_mass (risk : ℚ) (hvalid : ReferenceBudgetValid risk) (depth : ℕ+)
    (entry error : ℝ≥0∞)
    (herror : error ≤ ENNReal.ofReal ((controllerTarget risk depth.val : ℚ) : ℝ) * entry) :
    ENNReal.ofReal ((risk / 2 : ℚ) : ℝ) * entry +
      ENNReal.ofReal ((controllerBadRisk risk (controllerTarget risk depth.val) : ℚ) : ℝ) * error ≤
        ENNReal.ofReal (risk : ℝ) * entry :=
  referenceBudget_finiteBad_mass risk hvalid depth entry entry error le_rfl herror

/-- The actual infinite-rank branch keeps r regardless of the report and
has no fatal outcome. Here the two outcome masses need only sum to <=entry. -/
theorem referenceBudget_infiniteRank_mass (risk : ℚ) (entry good error : ℝ≥0∞)
    (hbranches : good + error ≤ entry) :
    ENNReal.ofReal (risk : ℝ) * good + ENNReal.ofReal (risk : ℝ) * error ≤ ENNReal.ofReal (risk : ℝ) * entry := by
  rw [← mul_add]
  exact mul_le_mul_right hbranches _

/-- Separate continuation and fatal weights of the actual Option update.
None is a fatal no-tool error, never a zero-risk continuation. -/
noncomputable def referenceBudgetContinuationWeight (kind : ReferenceBudgetCase) (error : Bool) (risk : ℚ) : ℝ≥0∞ :=
  match referenceBudgetStep kind error risk with
  | none => 0
  | some child => ENNReal.ofReal (child : ℝ)

def referenceBudgetFatalWeight (kind : ReferenceBudgetCase) (error : Bool) (risk : ℚ) : ℝ≥0∞ :=
  if (referenceBudgetStep kind error risk).isNone then 1 else 0

noncomputable def referenceBudgetOutcomeWeight (kind : ReferenceBudgetCase) (error : Bool) (risk : ℚ) : ℝ≥0∞ :=
  match referenceBudgetStep kind error risk with
  | none => 1
  | some child => ENNReal.ofReal (child : ℝ)

theorem referenceBudgetOutcomeWeight_eq (kind : ReferenceBudgetCase) (error : Bool) (risk : ℚ) :
    referenceBudgetOutcomeWeight kind error risk =
      referenceBudgetContinuationWeight kind error risk + referenceBudgetFatalWeight kind error risk := by
  cases hstep : referenceBudgetStep kind error risk <;>
    simp only [referenceBudgetOutcomeWeight, referenceBudgetContinuationWeight, referenceBudgetFatalWeight,
      hstep, Option.isNone_none, Option.isNone_some, Bool.false_eq_true, ite_false, ite_true, zero_add, add_zero]

def ReferenceBudgetMassBounds (kind : ReferenceBudgetCase) (risk : ℚ) (entry good error : ℝ≥0∞) : Prop :=
  match referenceBudgetTarget kind risk with
  | none => good + error ≤ entry
  | some target => good ≤ entry ∧ error ≤ ENNReal.ofReal (target : ℝ) * entry

/-- The unified one-stage budget-plus-failure bound refers directly to the
original target and update functions, and permits infinite entry masses. -/
theorem referenceBudget_one_step_mass (kind : ReferenceBudgetCase) (risk : ℚ) (hvalid : ReferenceBudgetValid risk)
    (entry good error : ℝ≥0∞) (hmass : ReferenceBudgetMassBounds kind risk entry good error) :
    referenceBudgetOutcomeWeight kind false risk * good + referenceBudgetOutcomeWeight kind true risk * error ≤
      ENNReal.ofReal (risk : ℝ) * entry := by
  cases kind with
  | infiniteRank =>
    exact referenceBudget_infiniteRank_mass risk entry good error hmass
  | noTool =>
    simpa only [referenceBudgetOutcomeWeight, referenceBudgetStep, Bool.false_eq_true, ite_false, ite_true, one_mul] using
      referenceBudget_noTool_mass risk hvalid.1.le entry good error hmass.1 hmass.2
  | finiteBad depth =>
    exact referenceBudget_finiteBad_mass risk hvalid depth entry good error hmass.1 hmass.2

theorem referenceBudget_continuation_fatal_mass (kind : ReferenceBudgetCase) (risk : ℚ)
    (hvalid : ReferenceBudgetValid risk) (entry good error : ℝ≥0∞)
    (hmass : ReferenceBudgetMassBounds kind risk entry good error) :
    (referenceBudgetContinuationWeight kind false risk * good + referenceBudgetContinuationWeight kind true risk * error) +
      (referenceBudgetFatalWeight kind false risk * good + referenceBudgetFatalWeight kind true risk * error) ≤
        ENNReal.ofReal (risk : ℝ) * entry := by
  calc
    _ = referenceBudgetOutcomeWeight kind false risk * good + referenceBudgetOutcomeWeight kind true risk * error := by
      rw [referenceBudgetOutcomeWeight_eq, referenceBudgetOutcomeWeight_eq]
      ring
    _ ≤ _ := referenceBudget_one_step_mass kind risk hvalid entry good error hmass

end PaperProofs.Statistics
