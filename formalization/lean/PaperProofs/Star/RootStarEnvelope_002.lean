module

public import PaperProofs.Star.RootStarEnvelope_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace RootStarEnvelope

open PaperProofs.Star PaperProofs.Star.Parameters PaperProofs.Statistics

theorem log_inverse_nonnegative (r : ℝ) (hr : 0 < r) (hq : r ≤ 1 / 4) :
    0 ≤ Real.log (1 / r) := by
  apply Real.log_nonneg
  exact (le_div_iff₀ hr).mpr (by linarith only [hq])

theorem envelope_nonnegative (P : Parameters) (k : ℕ) (r : ℝ)
    (hr : 0 < r) (hq : r ≤ 1 / 4) : 0 ≤ P.countObservationEnvelope k r := by
  induction k generalizing r with
  | zero => exact mul_nonneg P.channel.a_pos.le (add_nonneg (log_inverse_nonnegative r hr hq) P.channel.h_pos.le)
  | succ k ih =>
    have hp := RootStarQuota.starTarget_pos r (k + 1)
    have hquarter := RootStarQuota.starTarget_le_quarter r (k + 1)
    have hb := bad_bounds r hr hq (k + 1)
    change 0 ≤ P.channel.a * (Real.log (1 / starTargetReal r (k + 1)) + P.channel.h) +
      starTargetReal r (k + 1) * P.countObservationEnvelope k (badBudget r (k + 1))
    exact add_nonneg
      (mul_nonneg P.channel.a_pos.le (add_nonneg (log_inverse_nonnegative _ hp hquarter) P.channel.h_pos.le))
      (mul_nonneg hp.le (ih _ (bad_positive r hr (k + 1)) hb.2))

def EnvelopeBound (P : Parameters) (k : ℕ) : Prop :=
  ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
    |P.countObservationEnvelope k r - P.channel.a * iteratedLog (k + 1) (1 / r)| ≤ bound

theorem envelopeBound_zero (P : Parameters) : EnvelopeBound P 0 := by
  refine ⟨|P.channel.a * P.channel.h|, abs_nonneg _, Filter.Eventually.of_forall ?_⟩
  intro r
  have he : P.countObservationEnvelope 0 r - P.channel.a * iteratedLog 1 (1 / r) =
      P.channel.a * P.channel.h := by
    simp only [countObservationEnvelope, iteratedLog]
    ring
  simpa only [he] using (le_rfl : |P.channel.a * P.channel.h| ≤ |P.channel.a * P.channel.h|)

theorem weighted_envelope_bounded (P : Parameters) (k : ℕ) (ih : EnvelopeBound P k) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 ≤ starTargetReal r (k + 1) * P.countObservationEnvelope k (badBudget r (k + 1)) ∧
      starTargetReal r (k + 1) * P.countObservationEnvelope k (badBudget r (k + 1)) ≤ bound := by
  obtain ⟨B, hB, hcost⟩ := ih
  obtain ⟨A, hA, hlog⟩ := weighted_bad_iteratedLog_bounded (k + 1) (by omega)
  have hchild := (bad_tendsto_positive (k + 1) (by omega)).eventually hcost
  refine ⟨P.channel.a * A + (1 / 4) * B,
    add_nonneg (mul_nonneg P.channel.a_pos.le hA) (mul_nonneg (by norm_num) hB), ?_⟩
  filter_upwards [self_mem_nhdsWithin, eventually_quarter, hlog, hchild] with r hr hq hl hc
  have hp := RootStarQuota.starTarget_pos r (k + 1)
  have hquarter := RootStarQuota.starTarget_le_quarter r (k + 1)
  have hb := bad_bounds r hr hq (k + 1)
  have hn := envelope_nonnegative P k _ (bad_positive r hr (k + 1)) hb.2
  have hu := (abs_le.mp hc).2
  have hupper : P.countObservationEnvelope k (badBudget r (k + 1)) ≤
      P.channel.a * iteratedLog (k + 1) (1 / badBudget r (k + 1)) + B := by linarith only [hu]
  refine ⟨mul_nonneg hp.le hn, ?_⟩
  calc
    _ ≤ starTargetReal r (k + 1) *
        (P.channel.a * iteratedLog (k + 1) (1 / badBudget r (k + 1)) + B) :=
      mul_le_mul_of_nonneg_left hupper hp.le
    _ = P.channel.a * (starTargetReal r (k + 1) * iteratedLog (k + 1) (1 / badBudget r (k + 1))) +
        starTargetReal r (k + 1) * B := by ring
    _ ≤ P.channel.a * A + (1 / 4) * B :=
      add_le_add (mul_le_mul_of_nonneg_left hl.2.2 P.channel.a_pos.le)
        (mul_le_mul_of_nonneg_right hquarter hB)

theorem envelopeBound_succ (P : Parameters) (k : ℕ) (ih : EnvelopeBound P k) :
    EnvelopeBound P (k + 1) := by
  obtain ⟨B, hB, hlocal⟩ := bounded_of_tendsto (target_log_difference (k + 1) (by omega))
  obtain ⟨M, hM, hweighted⟩ := weighted_envelope_bounded P k ih
  refine ⟨P.channel.a * B + |P.channel.a * P.channel.h| + M,
    add_nonneg (add_nonneg (mul_nonneg P.channel.a_pos.le hB) (abs_nonneg _)) hM, ?_⟩
  filter_upwards [hlocal, hweighted] with r hl hw
  have he : P.countObservationEnvelope (k + 1) r - P.channel.a * iteratedLog ((k + 1) + 1) (1 / r) =
      (P.channel.a * (Real.log (1 / starTargetReal r (k + 1)) - iteratedLog ((k + 1) + 1) (1 / r)) +
        P.channel.a * P.channel.h) + starTargetReal r (k + 1) * P.countObservationEnvelope k (badBudget r (k + 1)) := by
    change P.channel.a * (Real.log (1 / starTargetReal r (k + 1)) + P.channel.h) +
      starTargetReal r (k + 1) * P.countObservationEnvelope k (badBudget r (k + 1)) -
        P.channel.a * iteratedLog ((k + 1) + 1) (1 / r) = _
    ring
  rw [he]
  calc
    _ ≤ |P.channel.a * (Real.log (1 / starTargetReal r (k + 1)) - iteratedLog ((k + 1) + 1) (1 / r)) +
          P.channel.a * P.channel.h| +
        |starTargetReal r (k + 1) * P.countObservationEnvelope k (badBudget r (k + 1))| := abs_add_le _ _
    _ ≤ (|P.channel.a * (Real.log (1 / starTargetReal r (k + 1)) - iteratedLog ((k + 1) + 1) (1 / r))| +
          |P.channel.a * P.channel.h|) +
        |starTargetReal r (k + 1) * P.countObservationEnvelope k (badBudget r (k + 1))| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = (P.channel.a * |Real.log (1 / starTargetReal r (k + 1)) - iteratedLog ((k + 1) + 1) (1 / r)| +
          |P.channel.a * P.channel.h|) +
        starTargetReal r (k + 1) * P.countObservationEnvelope k (badBudget r (k + 1)) := by
      rw [abs_mul, abs_of_pos P.channel.a_pos, abs_of_nonneg hw.1]
    _ ≤ P.channel.a * B + |P.channel.a * P.channel.h| + M :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hl P.channel.a_pos.le) le_rfl) hw.2

theorem envelopeBound_all (P : Parameters) : ∀ k : ℕ, EnvelopeBound P k
  | 0 => envelopeBound_zero P
  | k + 1 => envelopeBound_succ P k (envelopeBound_all P k)

end RootStarEnvelope
