module

public import PaperProofs.Star.RootStarQuota_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star
open PaperProofs.Star.Parameters PaperProofs.Statistics

theorem rat_quarter_cast (r : ℚ) (hq : r ≤ 1 / 4) : (r : ℝ) ≤ 1 / 4 := by
  have h : (r : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hq
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

theorem controllerTarget_cast (r : ℚ) (hr : 0 < r) (depth : ℕ) :
    (controllerTarget r depth : ℝ) = starTargetReal (r : ℝ) depth := by
  rw [controllerTarget_real, controllerB_eq_analytic r hr]
  rfl

theorem countTarget_cast (r : ℚ) (hr : 0 < r) (depth : ℕ) :
    (countTargetRat r depth : ℝ) = countTargetReal (r : ℝ) depth := by
  by_cases hd : depth = 0
  · simp [countTargetRat, countTargetReal, hd]
  · simp only [countTargetRat, countTargetReal, hd, ↓reduceIte]
    exact controllerTarget_cast r hr depth

theorem countBudget_cast (P : Parameters) (r : ℚ) (hr : 0 < r) (hq : r ≤ 1 / 4) (depth : ℕ) :
    (P.countBudgetRat r depth : ℝ) = P.countBudgetReal (r : ℝ) depth := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqR : (r : ℝ) ≤ 1 / 4 := rat_quarter_cast r hq
  induction depth with
  | zero => rfl
  | succ depth ih =>
    have hpos : 0 < P.countBudgetRat r depth := by
      have hb := (RootStarQuota.countBudget_bounds P (r : ℝ) hrR hqR depth).1
      have hpR : (0 : ℝ) < P.countBudgetRat r depth := by rw [ih]; exact hrR.trans_le hb
      exact_mod_cast hpR
    simp only [countBudgetRat, countBudgetReal, Rat.cast_min, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat, countTarget_cast _ hpos, ih]

theorem chosenTarget_cast (P : Parameters) (order : Order) (kind : PortKind) (r : ℚ)
    (hr : 0 < r) (hq : r ≤ 1 / 4)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage) :
    (P.chosenTargetRat order kind r history stage).map (fun q : ℚ => (q : ℝ)) =
      P.chosenTargetReal order kind (r : ℝ) history stage := by
  have hb := countBudget_cast P r hr hq stage.val
  have hp : 0 < P.countBudgetRat r stage.val := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hqR : (r : ℝ) ≤ 1 / 4 := rat_quarter_cast r hq
    have hposR : (0 : ℝ) < P.countBudgetRat r stage.val := by
      rw [hb]
      exact hrR.trans_le (RootStarQuota.countBudget_bounds P (r : ℝ) hrR hqR stage.val).1
    exact_mod_cast hposR
  have hc := countTarget_cast (P.countBudgetRat r stage.val) hp (P.tools - stage.val)
  rw [hb] at hc
  cases kind <;> cases order <;>
    simp only [chosenTargetRat, chosenTargetReal]
  all_goals split <;> simp [controllerTarget_cast r hr, hc, Rat.cast_min, Rat.cast_div]

theorem testingAction_rat_eq_real (P : Parameters) (order : Order) (kind : PortKind) (r : ℚ)
    (hr : 0 < r) (hq : r ≤ 1 / 4) (limit : Option ℕ)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage) :
    P.testingActionRat order kind r limit history stage =
      P.testingActionReal order kind (r : ℝ) limit history stage := by
  have hcast := chosenTarget_cast P order kind r hr hq history stage
  cases ht : P.chosenTargetRat order kind r history stage with
  | none =>
    simp only [ht, Option.map_none] at hcast
    simp only [testingActionRat, testingActionReal, ht, ← hcast]
  | some target =>
    simp only [ht, Option.map_some] at hcast
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hqR : (r : ℝ) ≤ 1 / 4 := rat_quarter_cast r hq
    have hb := RootStarQuota.chosenTarget_bounds P order kind (r : ℝ) hrR hqR history stage
      (target : ℝ) hcast.symm
    have htpos : 0 < target := by exact_mod_cast (show (0 : ℝ) < target by linarith [hb.1])
    have htone : target < 1 := by exact_mod_cast (show (target : ℝ) < 1 by linarith [hb.2])
    simp only [testingActionRat, testingActionReal, ht, ← hcast]
    split
    · rename_i hv
      dsimp only [historyObservationWord, Parameters.input] at ⊢
      simp only [← P.channel.experiment.rationalWordHits_iff target htpos htone,
        P.channel.experiment.rationalWordMAP_eq_recordDecision]
      rfl
    · rfl

theorem rationalStarImplementation (P : Parameters) : P.RationalStarImplementation := by
  intro order kind r hr hq limit history
  have heq : P.testingActionRat order kind r limit =
      P.testingActionReal order kind (r : ℝ) limit := by
    funext history stage
    exact testingAction_rat_eq_real P order kind r hr hq limit history stage
  simp only [starRationalRule, starReferenceRule, heq]

end RootStarOverflow
