module

public import PaperProofs.Star.RootStarLower_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics MeasureTheory
open scoped Topology ENNReal

namespace RootStarLower

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Statistics

theorem late_kind_lower (P : Parameters) (order : Order) (epsilon : ℝ) (he : 0 < epsilon) :
    KindLower P order .lateRetained epsilon := by
  let count : ℝ := (P.tools + 1 : ℕ)
  let cutoff : ℝ := Real.exp (-(2 * count / epsilon))
  refine ⟨cutoff, Real.exp_pos _, ?_⟩
  intro delta hd hs C hC accounting
  have hlog := Real.log_lt_log hd hs
  dsimp only [cutoff] at hlog
  rw [Real.log_exp] at hlog
  have hroom : 2 * count ≤ epsilon * Real.log delta⁻¹ := by
    rw [Real.log_inv]
    have hh : 2 * count / epsilon < -Real.log delta := by linarith only [hlog]
    have hm := (div_lt_iff₀ he).mp hh
    nlinarith only [hm]
  have hscaled := mul_le_mul_of_nonneg_left hroom P.channel.a_pos.le
  have hscalar : (1 - epsilon) * (P.channel.a * Real.log delta⁻¹) ≤
      P.channel.a * Real.log delta⁻¹ - 2 * P.channel.a * count := by
    nlinarith only [hscaled]
  change ENNReal.ofReal ((1 - epsilon) * (P.channel.a * Real.log delta⁻¹)) ≤
    value (P.input order) C .native accounting (ENNReal.ofReal delta)
  unfold value
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  have hobs := P.nativeLateObservationLower order C hC accounting Seed ‹MeasurableSpace Seed›
    ν ‹IsProbabilityMeasure ν› policy.val delta hd policy.property
  exact (ENNReal.ofReal_le_ofReal hscalar).trans
    (hobs.trans (expectedObservationBill_le_actual (P.input order) C .native accounting policy.val.rule ν))

theorem threePricesLower_of_retained_recursion (P : Parameters)
    (hrec : ∀ order : Order, PaperProofs.Retained.FreshPenaltyRecursion (P.input order)) :
    P.ThreePricesLower := by
  intro epsilon he _hlt
  obtain ⟨uc, huc, buc⟩ := current_kind_lower P .universalFirst epsilon he
  obtain ⟨sc, hsc, bsc⟩ := current_kind_lower P .singletonsFirst epsilon he
  obtain ⟨ue, hue, bue⟩ := early_kind_lower P .universalFirst (hrec .universalFirst) epsilon he
  obtain ⟨se, hse, bse⟩ := early_kind_lower P .singletonsFirst (hrec .singletonsFirst) epsilon he
  obtain ⟨ul, hul, bul⟩ := late_kind_lower P .universalFirst epsilon he
  obtain ⟨sl, hsl, bsl⟩ := late_kind_lower P .singletonsFirst epsilon he
  let cutoff := min uc (min sc (min ue (min se (min ul sl))))
  refine ⟨cutoff, lt_min huc (lt_min hsc (lt_min hue (lt_min hse (lt_min hul hsl)))), ?_⟩
  intro delta hd hs order kind C hC accounting
  have hall : delta < uc ∧ delta < sc ∧ delta < ue ∧ delta < se ∧ delta < ul ∧ delta < sl := by
    simpa only [cutoff, lt_min_iff] using hs
  obtain ⟨huc', hsc', hue', hse', hul', hsl'⟩ := hall
  cases order with
  | universalFirst =>
    cases kind with
    | current => exact buc delta hd huc' C hC accounting
    | earlyRetained => exact bue delta hd hue' C hC accounting
    | lateRetained => exact bul delta hd hul' C hC accounting
  | singletonsFirst =>
    cases kind with
    | current => exact bsc delta hd hsc' C hC accounting
    | earlyRetained => exact bse delta hd hse' C hC accounting
    | lateRetained => exact bsl delta hd hsl' C hC accounting

end RootStarLower
