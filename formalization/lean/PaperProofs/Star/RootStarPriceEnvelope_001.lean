module

public import PaperProofs.Star.RootStarEnvelope_003
public import PaperProofs.Statistics.IteratedLogComparison

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace RootStarPriceEnvelope

open PaperProofs.Star PaperProofs.Star.Parameters PaperProofs.Statistics

theorem half_tendsto_positive :
    Tendsto (fun delta : ℝ => delta / 2) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [zero_div, id_eq] using
      ((tendsto_id.div_const (2 : ℝ)).mono_left nhdsWithin_le_nhds :
        Tendsto (fun delta : ℝ => delta / 2) (𝓝[>] 0) (𝓝 ((0 : ℝ)/2)))
  · filter_upwards [self_mem_nhdsWithin] with delta positive
    exact div_pos positive (by norm_num)

theorem count_half_eventually (P : Parameters) (k : ℕ) (extra epsilon : ℝ) (he : 0 < epsilon) :
    ∀ᶠ delta : ℝ in 𝓝[>] 0,
      0 < P.channel.a * iteratedLog (k+1) delta⁻¹ ∧
        P.countObservationEnvelope k (delta/2) + extra ≤
          (1+epsilon) * (P.channel.a * iteratedLog (k+1) delta⁻¹) := by
  obtain ⟨B, _nonneg, bound⟩ := RootStarEnvelope.envelopeBound_all P k
  have boundHalf := half_tendsto_positive.eventually bound
  have ratio := (iteratedLog_scale_div_tendsto_one (k+1) (by omega) 2 (by norm_num)).comp
    RootStarEnvelope.inverse_tendsto
  have ratioUpper := ratio.eventually (eventually_lt_nhds (by linarith : (1 : ℝ) < 1+epsilon/2))
  have growth : Tendsto (fun delta : ℝ => iteratedLog (k+1) delta⁻¹) (𝓝[>] 0) atTop := by
    simpa only [Function.comp_def, one_div] using
      (iteratedLog_tendsto_atTop (k+1)).comp RootStarEnvelope.inverse_tendsto
  have positive := growth.eventually_gt_atTop 0
  have absorb := (growth.const_mul_atTop (mul_pos (by linarith : 0 < epsilon/2) P.channel.a_pos)).eventually_ge_atTop (B+extra)
  filter_upwards [boundHalf, ratioUpper, positive, absorb, self_mem_nhdsWithin] with delta hb hratio hl hlarge hd
  have scalePositive := mul_pos P.channel.a_pos hl
  have ratioBound : iteratedLog (k+1) (1/(delta/2)) ≤
      (1+epsilon/2) * iteratedLog (k+1) delta⁻¹ := by
    have ratioBound' : iteratedLog (k+1) (2*delta⁻¹) / iteratedLog (k+1) delta⁻¹ ≤ 1+epsilon/2 := by
      simpa only [Function.comp_def, one_div] using hratio.le
    have identity : 1/(delta/2) = 2*delta⁻¹ := by ring
    rw [identity]
    exact (div_le_iff₀ hl).mp ratioBound'
  refine ⟨scalePositive, ?_⟩
  have bound' := (abs_le.mp hb).2
  have comparison := mul_le_mul_of_nonneg_left ratioBound P.channel.a_pos.le
  nlinarith only [bound', comparison, hlarge]

noncomputable def observationEnvelope (P : Parameters) (order : Order) (kind : PortKind) (delta : ℝ) : ℝ :=
  match kind, order with
  | .lateRetained, _ => P.channel.a * (Real.log (1/(delta/2)) + P.channel.h)
  | .current, .universalFirst => P.currentObservationEnvelope (delta/2)
  | _, _ => P.countObservationEnvelope P.tools (delta/2)

/-- One cutoff for all original orders and contracts, with the actual
reference budget delta/2 and all possible correction charges included. -/
theorem uniform_upper (P : Parameters) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ delta : ℝ, 0 < delta → delta < cutoff → delta ≤ 1/2 →
      ∀ (order : Order) (kind : PortKind), 0 < P.leadingScale order kind delta ∧
        observationEnvelope P order kind delta + (P.tools : ℝ) * (P.correctionFee : ℝ) ≤
          (1+epsilon) * P.leadingScale order kind delta := by
  have lr := count_half_eventually P 0 ((P.tools : ℝ)*(P.correctionFee : ℝ)) epsilon he
  have uf := count_half_eventually P 1 ((P.tools : ℝ)*(P.correctionFee : ℝ)) epsilon he
  have count := count_half_eventually P P.tools ((P.tools : ℝ)*(P.correctionFee : ℝ)) epsilon he
  have allCases : ∀ᶠ delta : ℝ in 𝓝[>] 0, ∀ (order : Order) (kind : PortKind),
      0 < P.leadingScale order kind delta ∧
        observationEnvelope P order kind delta + (P.tools : ℝ)*(P.correctionFee : ℝ) ≤
          (1+epsilon) * P.leadingScale order kind delta := by
    filter_upwards [lr, uf, count] with delta hlr huf hc
    intro order kind
    cases kind <;> cases order
    all_goals simp only [leadingScale, priceDepth, observationEnvelope]
    · simpa only [Nat.reduceAdd, currentObservationEnvelope, countObservationEnvelope, mul_assoc] using huf
    · exact hc
    · exact hc
    · exact hc
    · simpa only [Nat.reduceAdd, countObservationEnvelope] using hlr
    · simpa only [Nat.reduceAdd, countObservationEnvelope] using hlr
  obtain ⟨cutoff, positive, below⟩ := RootStarEnvelope.positive_cutoff allCases
  exact ⟨cutoff, positive, fun delta hd ht _ => below delta hd ht⟩

end RootStarPriceEnvelope
