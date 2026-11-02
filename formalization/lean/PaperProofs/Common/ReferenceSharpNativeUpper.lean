module

public import PaperProofs.Common.ReferenceCostAsymptotics
public import PaperProofs.Common.ReferenceNativeRisk

/-!
The original finite-rank native upper law. Its real-delta cutoff is uniform
over every original rational risk choice and every qualified native contract.
No choice function, comparison-policy certificate, or performance premise is
introduced. The controller's original complete-execution H0 remains required.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PaperProofs.Statistics

/-- A uniform comparison for ALL real targets in the original factor-two
interval. No choice function or regularity of a rationalization is needed. -/
theorem iteratedLog_factorTwo_uniform_cutoff (depth : ℕ) (hdepth : 1 ≤ depth)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ (delta target : ℝ),
      0 < delta → delta < cutoff → delta / 2 ≤ target → target ≤ delta →
      0 < iteratedLog depth (1 / delta) ∧
        iteratedLog depth (1 / target) ≤ (1 + eta) * iteratedLog depth (1 / delta) := by
  obtain ⟨threshold, _hthreshold, hmono⟩ := iteratedLog_positive_mono_tail depth
  have hratio := (iteratedLog_scale_div_tendsto_one depth hdepth 2 (by norm_num)).eventually
    (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + eta))
  obtain ⟨ratioThreshold, hratioThreshold⟩ := eventually_atTop.mp hratio
  let large := max threshold (max ratioThreshold 1)
  have hlargePositive : 0 < large := by dsimp [large]; exact lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨1 / large, one_div_pos.mpr hlargePositive, ?_⟩
  intro delta target hdelta hcut hlower hupper
  have htarget : 0 < target := lt_of_lt_of_le (half_pos hdelta) hlower
  have hlarge : large ≤ 1 / delta := by
    apply le_of_lt
    apply (lt_div_iff₀ hdelta).mpr
    have hm := (lt_div_iff₀ hlargePositive).mp hcut
    nlinarith
  have hbase : threshold ≤ 1 / delta := (le_max_left _ _).trans hlarge
  have hratioInput : ratioThreshold ≤ 1 / delta :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hlowerInv : 1 / delta ≤ 1 / target := one_div_le_one_div_of_le htarget hupper
  have hupperInv : 1 / target ≤ 2 * (1 / delta) := by
    calc
      _ ≤ 1 / (delta / 2) := one_div_le_one_div_of_le (half_pos hdelta) hlower
      _ = _ := by field_simp
  have hpositive := (hmono _ _ hbase le_rfl).1
  have hmonotone := (hmono _ _ (hbase.trans hlowerInv) hupperInv).2
  have hscaled := (div_lt_iff₀ hpositive).mp (hratioThreshold _ hratioInput)
  exact ⟨hpositive, hmonotone.trans hscaled.le⟩

end PaperProofs.Statistics

namespace PaperProofs.Common

open PaperProofs.Statistics PaperProofs.Structure Native

variable {I : Instance}

/-- The original finite-rank native upper price law, now proved from the
actual original reference asymptotics, risk, truncation and cap transfer. -/
theorem StatisticalInput.nativeUpperPriceLaw (input : StatisticalInput I) :
    input.NativeUpperPriceLaw := by
  intro depth hrank epsilon hepsilon
  have hfinite : errorRank I.compatibility I.tools ≠ ⊤ := by rw [hrank]; exact ENat.natCast_ne_top depth
  have hcoefficient := input.orderedCoefficient_pos I.tools hfinite
  have hdepth : 1 ≤ depth := by
    have hp := errorRank_pos I.compatibility I.tools
    rw [hrank] at hp
    have : 0 < depth := by exact_mod_cast hp
    omega
  let eta := min (epsilon / 4) 1
  have heta : 0 < eta := lt_min (by positivity) (by norm_num)
  have hetaOne : eta ≤ 1 := min_le_right _ _
  have hetaEpsilon : eta ≤ epsilon / 4 := min_le_left _ _
  have hproduct : (1 + eta) * (1 + eta) ≤ 1 + epsilon := by
    have hsquare : eta * eta ≤ eta := by nlinarith
    nlinarith
  obtain ⟨costCutoff, hcostCutoff, hcost⟩ := referenceCostAsymptotics input I.tools depth hrank eta heta
  obtain ⟨logCutoff, hlogCutoff, hlogs⟩ := iteratedLog_factorTwo_uniform_cutoff depth hdepth eta heta
  refine ⟨min costCutoff logCutoff, lt_min hcostCutoff hlogCutoff, ?_⟩
  intro delta exponent budget hdelta hcut hsmall choice C hcurrent accounting qualification
  have hbudgetCut : (budget : ℝ) < costCutoff :=
    choice.conservative.trans_lt (hcut.trans_le (min_le_left _ _))
  have hlog := hlogs delta (budget : ℝ) hdelta (hcut.trans_le (min_le_right _ _))
    choice.factor_two choice.conservative
  have hbill := hcost budget choice.positive choice.small hbudgetCut C hcurrent accounting
  calc
    _ ≤ expectedBill input C .uncapped accounting
        (referenceIdealPolicy input C hcurrent.1 accounting I.tools budget).rule (Measure.dirac ()) :=
      native_value_le_reference_ideal input C hcurrent accounting delta hdelta hsmall exponent budget choice qualification
    _ ≤ ENNReal.ofReal ((1 + eta) * input.orderedCoefficient I.tools *
        iteratedLog depth (budget : ℝ)⁻¹) := hbill
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      calc
        _ ≤ (1 + eta) * input.orderedCoefficient I.tools *
            ((1 + eta) * iteratedLog depth (1 / delta)) :=
          mul_le_mul_of_nonneg_left (by simpa only [one_div] using hlog.2) (by positivity)
        _ = ((1 + eta) * (1 + eta)) * input.orderedCoefficient I.tools * iteratedLog depth (1 / delta) := by ring
        _ ≤ _ := by
          simpa only [one_div] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hproduct hcoefficient.le) hlog.1.le)

/-- The original infinite-rank native law, for arbitrary original budget and
exponent under precisely the original qualification. No finite-rank risk
choice is required. The witness is the actual bounded controller with caps
enforced by its original complete-execution H0 and numeric certificates. -/
theorem StatisticalInput.nativeInfiniteRankPriceLaw (input : StatisticalInput I) :
    input.NativeInfiniteRankPriceLaw := by
  intro htop C hcurrent accounting budget exponent hbudget hsmall qualification
  let bounded := referenceBoundedPolicy input C hcurrent.1 accounting I.tools budget exponent
  let reviews := referenceReviewBounds input C hcurrent.1 accounting I.tools budget exponent hbudget hsmall
  let native := bounded.enforceCaps input C accounting (referenceQuota input exponent)
    reviews qualification.normal_calls qualification.stage_quota qualification.total_calls
  have heq (sample : Unit × input.World) (n : ℕ) :
      run input C .native accounting native.rule sample n =
        run input C .uncapped accounting bounded.rule sample n :=
    enforceCaps_run_eq input C accounting bounded (referenceQuota input exponent)
      reviews qualification.normal_calls qualification.stage_quota qualification.total_calls sample n
  have hzeroObservation : expectedObservationBill input C .native accounting native.rule (Measure.dirac ()) = 0 := by
    calc
      _ = expectedObservationBill input C .uncapped accounting bounded.rule (Measure.dirac ()) := by
        unfold expectedObservationBill runObservationBill
        simp_rw [heq]
      _ = 0 := referenceExpectedObservationBill_infiniteRank input C hcurrent.1 accounting I.tools budget
        hbudget hsmall htop (some (referenceQuota input exponent)) (Measure.dirac ())
  refine ⟨native, ?_, hzeroObservation, ?_⟩
  · calc
      _ = risk input C .uncapped accounting bounded.rule (Measure.dirac ()) :=
        enforceCaps_risk_eq input C accounting bounded (referenceQuota input exponent)
          reviews qualification.normal_calls qualification.stage_quota qualification.total_calls (Measure.dirac ())
      _ = 0 := referenceRisk_zero_of_infinite_rank input C hcurrent.1 accounting I.tools budget
        hbudget hsmall htop (some (referenceQuota input exponent)) (Measure.dirac ())
  · have hbill := expectedBill_le_observation_add input C .native accounting native (Measure.dirac ())
    rw [hzeroObservation, zero_add] at hbill
    exact hbill

end PaperProofs.Common
