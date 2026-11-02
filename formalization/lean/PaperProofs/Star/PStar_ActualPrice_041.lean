module

public import PaperProofs.Star.Claims
public import PaperProofs.Common.NativeSeed
public import PaperProofs.Star.RootStarPriceEnvelope_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarActualPrice041

open Common Common.Native Parameters MeasureTheory
open scoped ENNReal

/-- The actual original ideal observation costs and all-path charges,
uniformly over the original six order/contract cases. -/
theorem idealBounds_of_constructions (P : PaperProofs.Star.Parameters)
    (universal : P.UniversalFirstCurrentConstruction) (count : P.CountControllerConstruction)
    (late : P.LateRetainedConstruction) (order : Order) (kind : PortKind)
    (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order))
    (delta : ℝ) (positive : 0 < delta) (small : delta ≤ 1/2) :
    expectedObservationBill (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind (delta/2) none (Seed := Unit)) (Measure.dirac ()) ≤
        ENNReal.ofReal (RootStarPriceEnvelope.observationEnvelope P order kind delta) ∧
    P.ReferenceAllPathCharges order kind (delta/2) none C accounting := by
  have budgetPositive : 0 < delta/2 := by linarith
  have budgetSmall : delta/2 ≤ 1/4 := by linarith
  cases kind with
  | current =>
    cases order with
    | universalFirst =>
      rcases universal C qualified accounting (delta/2) budgetPositive budgetSmall with
        ⟨_legal, _risk, observation, _immediate, _identities, charges⟩
      exact ⟨observation, charges⟩
    | singletonsFirst =>
      rcases count .singletonsFirst .current (Or.inr ⟨rfl, rfl⟩) C qualified accounting
        (delta/2) budgetPositive budgetSmall with
        ⟨_legal, _risk, observation, _terminal, _noEarly, _identities, charges⟩
      exact ⟨observation, charges⟩
  | earlyRetained =>
    rcases count order .earlyRetained (Or.inl rfl) C qualified accounting
      (delta/2) budgetPositive budgetSmall with
      ⟨_legal, _risk, observation, _terminal, _noEarly, _identities, charges⟩
    cases order <;> exact ⟨observation, charges⟩
  | lateRetained =>
    rcases late order C qualified accounting (delta/2) budgetPositive budgetSmall with
      ⟨_legal, _risk, observation, _otherZero, _noEarly, _terminal, charges⟩
    cases order <;> exact ⟨observation, charges⟩

theorem observationEnvelope_nonnegative (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (delta : ℝ) (positive : 0 < delta) (small : delta ≤ 1/2) :
    0 ≤ RootStarPriceEnvelope.observationEnvelope P order kind delta := by
  have budgetPositive : 0 < delta/2 := by linarith
  have budgetSmall : delta/2 ≤ 1/4 := by linarith
  cases kind <;> cases order
  all_goals simp only [RootStarPriceEnvelope.observationEnvelope]
  · simpa only [currentObservationEnvelope, countObservationEnvelope, mul_assoc] using
      RootStarEnvelope.envelope_nonnegative P 1 (delta/2) budgetPositive budgetSmall
  · exact RootStarEnvelope.envelope_nonnegative P P.tools (delta/2) budgetPositive budgetSmall
  · exact RootStarEnvelope.envelope_nonnegative P P.tools (delta/2) budgetPositive budgetSmall
  · exact RootStarEnvelope.envelope_nonnegative P P.tools (delta/2) budgetPositive budgetSmall
  · exact RootStarEnvelope.envelope_nonnegative P 0 (delta/2) budgetPositive budgetSmall
  · exact RootStarEnvelope.envelope_nonnegative P 0 (delta/2) budgetPositive budgetSmall

/-- Include every actual correction fee on every path before comparison
with the native all-policy value. No termination or finite-cost input. -/
theorem idealActualBill_le_envelope (P : PaperProofs.Star.Parameters)
    (universal : P.UniversalFirstCurrentConstruction) (count : P.CountControllerConstruction)
    (late : P.LateRetainedConstruction) (order : Order) (kind : PortKind)
    (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order))
    (delta : ℝ) (positive : 0 < delta) (small : delta ≤ 1/2) :
    expectedBill (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind (delta/2) none (Seed := Unit)) (Measure.dirac ()) ≤
        ENNReal.ofReal (RootStarPriceEnvelope.observationEnvelope P order kind delta +
          (P.tools : ℝ)*(P.correctionFee : ℝ)) := by
  obtain ⟨observation, charges⟩ := idealBounds_of_constructions P universal count late order kind
    C qualified accounting delta positive small
  have allPath := lintegral_mono (μ := (P.input order).seededWorldLaw (Measure.dirac ()))
    (fun sample => (charges sample).2)
  rw [lintegral_add_left (measurable_runObservationBill (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind (delta/2) none) (P.measurable_starReferenceRule order kind (delta/2) none))] at allPath
  simp only [lintegral_const, measure_univ, mul_one] at allPath
  have feeNonnegative : 0 ≤ (P.tools : ℝ)*(P.correctionFee : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast P.correctionFee_nonneg)
  calc
    _ ≤ expectedObservationBill (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind (delta/2) none) (Measure.dirac ()) +
          (P.tools : ℝ≥0∞)*ENNReal.ofReal (P.correctionFee : ℝ) := allPath
    _ ≤ ENNReal.ofReal (RootStarPriceEnvelope.observationEnvelope P order kind delta) +
          (P.tools : ℝ≥0∞)*ENNReal.ofReal (P.correctionFee : ℝ) := add_le_add observation le_rfl
    _ = ENNReal.ofReal (RootStarPriceEnvelope.observationEnvelope P order kind delta +
          (P.tools : ℝ)*(P.correctionFee : ℝ)) := by
      rw [ENNReal.ofReal_add (observationEnvelope_nonnegative P order kind delta positive small) feeNonnegative, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end PaperProofs.Star.PStarActualPrice041

