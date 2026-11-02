module

public import PaperProofs.Star.RootStarEnvelope_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace RootStarEnvelope

open PaperProofs.Star PaperProofs.Star.Parameters PaperProofs.Statistics

theorem universalFirstEnvelopeAsymptotics (P : Parameters) : P.UniversalFirstEnvelopeAsymptotics := by
  constructor
  · intro r _hr _hq
    exact target_product_le r 1
  · obtain ⟨B, hB, hbound⟩ := envelopeBound_all P 1
    obtain ⟨cutoff, hcutoff, hsmall⟩ := positive_cutoff hbound
    refine ⟨B, cutoff, hB, hcutoff, ?_⟩
    intro r hr _hq hs
    simpa only [currentObservationEnvelope, countObservationEnvelope, mul_assoc] using hsmall r hr hs

theorem envelope_relative_upper (P : Parameters) (k : ℕ) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ r : ℝ, 0 < r → r < cutoff →
      P.countObservationEnvelope k r ≤ (1 + epsilon) * P.channel.a * iteratedLog (k + 1) (1 / r) := by
  obtain ⟨B, _hB, hbound⟩ := envelopeBound_all P k
  have hlarge := (((iteratedLog_tendsto_atTop (k + 1)).comp inverse_tendsto).const_mul_atTop
    (mul_pos he P.channel.a_pos)).eventually_ge_atTop B
  obtain ⟨cutoff, hcutoff, hsmall⟩ := positive_cutoff (hbound.and hlarge)
  refine ⟨cutoff, hcutoff, ?_⟩
  intro r hr hs
  obtain ⟨ha, hl⟩ := hsmall r hr hs
  have hu := (abs_le.mp ha).2
  calc
    _ ≤ P.channel.a * iteratedLog (k + 1) (1 / r) + B := by linarith only [hu]
    _ ≤ P.channel.a * iteratedLog (k + 1) (1 / r) +
        epsilon * P.channel.a * iteratedLog (k + 1) (1 / r) := add_le_add le_rfl hl
    _ = _ := by ring

theorem countEnvelopeAsymptotics (P : Parameters) : P.CountEnvelopeAsymptotics := by
  constructor
  · intro k hk _hkt
    obtain ⟨B, hB, hweighted⟩ := weighted_envelope_bounded P (k - 1) (envelopeBound_all P (k - 1))
    have hweighted' : ∀ᶠ r : ℝ in 𝓝[>] 0,
        starTargetReal r k * P.countObservationEnvelope (k - 1) (min (1 / 4) (r / starTargetReal r k)) ≤ B := by
      simpa only [Nat.sub_add_cancel hk, badBudget] using hweighted.mono (fun _ hr => hr.2)
    obtain ⟨cutoff, hcutoff, hsmall⟩ := positive_cutoff hweighted'
    exact ⟨B, cutoff, hB, hcutoff, fun r hr _hq hs => hsmall r hr hs⟩
  · intro k _hk epsilon he
    obtain ⟨cutoff, hcutoff, hsmall⟩ := envelope_relative_upper P k epsilon he
    exact ⟨cutoff, hcutoff, fun r hr _hq hs => hsmall r hr hs⟩

end RootStarEnvelope
