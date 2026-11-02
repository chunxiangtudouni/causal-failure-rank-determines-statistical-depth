module

public import PaperProofs.Star.RootStarEnvelope_003
public import PaperProofs.Star.PStar_UniversalConstruction_039
public import PaperProofs.Statistics.IteratedLogComparison

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarRawScope044

open Common Common.Native Statistics Parameters Filter MeasureTheory
open scoped Topology ENNReal

/-- The additive shift needed by the frozen manuscript's ORIGINAL
r0=delta/2 universal-first display, rather than only relative equivalence. -/
theorem iteratedLog_two_dilation_sub_tendsto_zero :
    Tendsto (fun z : ℝ => iteratedLog 2 (2*z) - iteratedLog 2 z) atTop (𝓝 0) := by
  have ratio := iteratedLog_scale_div_tendsto_one 1 (by omega) 2 (by norm_num)
  have logged := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp ratio
  have loggedZero : Tendsto (fun z : ℝ => Real.log (iteratedLog 1 (2*z)/iteratedLog 1 z)) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using logged
  apply loggedZero.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with z hz
  change Real.log (Real.log (2*z)/Real.log z) = Real.log (Real.log (2*z)) - Real.log (Real.log z)
  exact Real.log_div (ne_of_gt (Real.log_pos (by linarith))) (ne_of_gt (Real.log_pos (by linarith)))

/-- Exactly the delta-normalized additive O(1) assertion in C:105--109.
One fixed bound and cutoff precede delta and every contract/accounting. -/
theorem universalFirst_half_additive_bound (P : PaperProofs.Star.Parameters) :
    ∃ bound cutoff : ℝ, 0 ≤ bound ∧ 0 < cutoff ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → delta < cutoff →
        |P.currentObservationEnvelope (delta/2) - P.channel.a*iteratedLog 2 delta⁻¹| ≤ bound := by
  obtain ⟨bound, cutoff, boundNonnegative, cutoffPositive, boundAtBudget⟩ :=
    (RootStarEnvelope.universalFirstEnvelopeAsymptotics P).2
  have shifted := iteratedLog_two_dilation_sub_tendsto_zero.comp RootStarEnvelope.inverse_tendsto
  have scaled : Tendsto (fun delta : ℝ => P.channel.a *
      (iteratedLog 2 (delta/2)⁻¹ - iteratedLog 2 delta⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    simp only [inv_div]
    simpa only [Function.comp_def, one_div, div_eq_mul_inv, one_mul, mul_zero] using shifted.const_mul P.channel.a
  have shiftSmall : ∀ᶠ delta : ℝ in 𝓝[>] 0,
      |P.channel.a*(iteratedLog 2 (delta/2)⁻¹ - iteratedLog 2 delta⁻¹)| ≤ 1 := by
    have boundOne := scaled.abs.eventually (eventually_lt_nhds (by norm_num : |(0 : ℝ)| < 1))
    exact boundOne.mono (fun _ h => h.le)
  obtain ⟨shiftCutoff, shiftPositive, shiftBound⟩ := RootStarEnvelope.positive_cutoff shiftSmall
  refine ⟨bound+1, min cutoff shiftCutoff, by linarith, lt_min cutoffPositive shiftPositive, ?_⟩
  intro delta positive small below
  have budgetPositive : 0 < delta/2 := by linarith
  have budgetSmall : delta/2 ≤ 1/4 := by linarith
  have budgetBelow : delta/2 < cutoff := by
    have : delta < cutoff := below.trans_le (min_le_left _ _)
    linarith
  have budgetBound := boundAtBudget (delta/2) budgetPositive budgetSmall budgetBelow
  have deltaShift := shiftBound delta positive (below.trans_le (min_le_right _ _))
  calc
    _ = |(P.currentObservationEnvelope (delta/2) - P.channel.a*iteratedLog 2 (delta/2)⁻¹) +
          P.channel.a*(iteratedLog 2 (delta/2)⁻¹ - iteratedLog 2 delta⁻¹)| := by congr 1; ring
    _ ≤ |P.currentObservationEnvelope (delta/2) - P.channel.a*iteratedLog 2 (delta/2)⁻¹| +
          |P.channel.a*(iteratedLog 2 (delta/2)⁻¹ - iteratedLog 2 delta⁻¹)| := abs_add_le _ _
    _ ≤ bound+1 := add_le_add (by simpa only [one_div] using budgetBound) deltaShift

/-- The same manuscript display applied to the true original observation
bill, retaining all failing-path observations and arbitrary original I caps. -/
theorem universalFirst_actualObservation_half_le_additive (P : PaperProofs.Star.Parameters) :
    ∃ bound cutoff : ℝ, 0 ≤ bound ∧ 0 < cutoff ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → delta < cutoff →
        ∀ (C : Contract (starInstance P.tools .universalFirst)), C.IsCurrentAllocation →
          ∀ accounting, expectedObservationBill (P.input .universalFirst) C .uncapped accounting
            (P.starReferenceRule .universalFirst .current (delta/2) none (Seed := Unit)) (Measure.dirac ()) ≤
            ENNReal.ofReal (P.channel.a*iteratedLog 2 delta⁻¹ + bound) := by
  obtain ⟨bound, cutoff, boundNonnegative, cutoffPositive, uniformBound⟩ := universalFirst_half_additive_bound P
  refine ⟨bound, cutoff, boundNonnegative, cutoffPositive, ?_⟩
  intro delta positive small below C current accounting
  have observation := (PStarUniversalConstruction039.universalFirstCurrentConstruction P
    C current accounting (delta/2) (by linarith) (by linarith)).2.2.1
  apply observation.trans (ENNReal.ofReal_le_ofReal ?_)
  have upper := (abs_le.mp (uniformBound delta positive small below)).2
  linarith

end PaperProofs.Star.PStarRawScope044

