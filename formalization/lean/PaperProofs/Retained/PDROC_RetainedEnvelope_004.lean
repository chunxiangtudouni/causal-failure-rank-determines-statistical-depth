module

public import PaperProofs.Retained.PDROC_RetainedEnvelope_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PaperProofs.Retained.PRetObservationEnvelope119

open Common Common.Native Statistics MeasureTheory Filter
open scoped ENNReal Topology
open RootRetainedAsymp

variable {I : Instance}

def EnvelopeScaleBound (input : StatisticalInput I) (next : ℕ)
    (old : Finset I.Stage) (depth : ℕ) : Prop :=
  ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
    observationEnvelopeReal input next old risk ≤ coefficient * iteratedLog depth (1 / (risk : ℝ))

theorem good_scale_bound (input : StatisticalInput I) (stage : I.Stage)
    (ih : ∀ old, Healthy I (stage.val + 1) old → ∀ depth : ℕ,
      errorRank I (stagesFrom I (stage.val + 1)) old = (depth : ℕ∞) →
        EnvelopeScaleBound input (stage.val + 1) old depth)
    (old : Finset I.Stage) (hh : Healthy I stage.val old) (depth : ℕ)
    (hr : errorRank I (stagesFrom I stage.val) old = (depth : ℕ∞)) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      observationEnvelopeReal input (stage.val + 1) old (risk / 2) ≤
        coefficient * iteratedLog depth (1 / (risk : ℝ)) := by
  have hd : 1 ≤ depth := by
    have hp := rank_positive (stagesFrom I stage.val) old hh.2.2
    rw [hr] at hp
    have : 0 < depth := by exact_mod_cast hp
    omega
  by_cases ht : errorRank I (stagesFrom I (stage.val + 1)) old = ⊤
  · refine ⟨1, by norm_num, ?_⟩
    have hp := ((iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop).eventually_ge_atTop 0
    filter_upwards [hp] with risk hp
    change 0 ≤ iteratedLog depth (1 / (risk : ℝ)) at hp
    simpa only [observationEnvelopeReal, observationEnvelope_zero_of_rank_top input _ old _ ht,
      ENNReal.toReal_zero, one_mul] using hp
  · obtain ⟨higher, hk⟩ := ENat.ne_top_iff_exists.mp ht
    obtain ⟨coefficient, hc, hb⟩ := ih old (healthy_correct I stage old hh) higher hk.symm
    have horder : depth ≤ higher := ENat.natCast_le_natCast.mp (by
      simpa only [hr, ← hk] using rank_le_good stage old hh)
    exact ⟨2 * coefficient, by positivity,
      half_scale_bound _ coefficient hc.le depth higher hd horder hb⟩

theorem envelopeScaleBound_step (input : StatisticalInput I) (stage : I.Stage)
    (ih : ∀ old, Healthy I (stage.val + 1) old → ∀ depth : ℕ,
      errorRank I (stagesFrom I (stage.val + 1)) old = (depth : ℕ∞) →
        EnvelopeScaleBound input (stage.val + 1) old depth)
    (old : Finset I.Stage) (hh : Healthy I stage.val old) (depth : ℕ)
    (hr : errorRank I (stagesFrom I stage.val) old = (depth : ℕ∞)) :
    EnvelopeScaleBound input stage.val old depth := by
  obtain ⟨goodCoefficient, hgoodPositive, hgood⟩ := good_scale_bound input stage ih old hh depth hr
  rcases finite_rank_cases stage old hh depth hr with ⟨hc, rfl⟩ | ⟨j, hc, hhealthy, hbadRank, horder⟩
  · refine ⟨(input.experiment stage).coefficient + 1 + goodCoefficient, by
      have := (input.experiment stage).coefficient_pos
      linarith, ?_⟩
    filter_upwards [localPriceReal_noTool_eventual input stage 1 (by norm_num), hgood,
      self_mem_nhdsWithin, rationalRisk_eventually_le_quarter] with risk hl hg hp hq
    rw [observationEnvelopeReal_noTool input stage old risk ⟨hp, hq⟩ hc]
    nlinarith
  · have hd : 1 ≤ depth := by
      have h := rank_positive (stagesFrom I stage.val) old hh.2.2
      rw [hr] at h
      have : 0 < depth := by exact_mod_cast h
      omega
    obtain ⟨badCoefficient, hbadPositive, hbad⟩ := ih (insert stage old) hhealthy j.val hbadRank
    obtain ⟨bound, hbound, hweighted⟩ := bad_scale_bound _ badCoefficient hbadPositive.le j hbad
    have hlocal := localPriceReal_finiteBad_eventual input stage j depth hd horder 1 (by norm_num)
    have hlarge := ((iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop).eventually_ge_atTop 1
    refine ⟨(input.experiment stage).coefficient + 1 + goodCoefficient + bound, by
      have := (input.experiment stage).coefficient_pos
      linarith, ?_⟩
    filter_upwards [hlocal, hgood, hweighted, hlarge, self_mem_nhdsWithin,
      rationalRisk_eventually_le_quarter] with risk hl hg hb hL hp hq
    change 1 ≤ iteratedLog depth (1 / (risk : ℝ)) at hL
    rw [observationEnvelopeReal_finiteBad input stage old risk ⟨hp, hq⟩ j hc]
    have hi : (input.experiment stage).coefficient * (if depth = j.val + 1 then 1 else 0) ≤
        (input.experiment stage).coefficient := by
      split_ifs
      · simp only [mul_one, le_refl]
      · simpa only [mul_zero] using (input.experiment stage).coefficient_pos.le
    have hl' : (localObservationPrice input stage (.finiteBad j) risk).toReal ≤
        ((input.experiment stage).coefficient + 1) * iteratedLog depth (1 / (risk : ℝ)) :=
      hl.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
    have hB : bound ≤ bound * iteratedLog depth (1 / (risk : ℝ)) := by nlinarith
    nlinarith

theorem observationEnvelope_scaleBound (input : StatisticalInput I) (next : ℕ)
    (old : Finset I.Stage) (hh : Healthy I next old) (depth : ℕ)
    (hr : errorRank I (stagesFrom I next) old = (depth : ℕ∞)) :
    EnvelopeScaleBound input next old depth := by
  have hall : ∀ fuel : ℕ, ∀ next : ℕ, I.stageCount - next = fuel →
      ∀ old, Healthy I next old → ∀ depth : ℕ,
        errorRank I (stagesFrom I next) old = (depth : ℕ∞) →
          EnvelopeScaleBound input next old depth := by
    intro fuel
    induction fuel with
    | zero =>
      intro next hf old hh depth hr
      have hn : I.stageCount ≤ next := Nat.sub_eq_zero_iff_le.mp hf
      have ht := rank_past_end_top next old hn hh.2.2
      rw [ht] at hr
      exact (ENat.top_ne_natCast depth hr).elim
    | succ fuel ih =>
      intro next hf old hh depth hr
      have hn : next < I.stageCount := by omega
      let stage : I.Stage := ⟨next, hn⟩
      have hchild : I.stageCount - (stage.val + 1) = fuel := by dsimp only [stage]; omega
      exact envelopeScaleBound_step input stage
        (fun childOld childHealthy childDepth childRank =>
          ih (stage.val + 1) hchild childOld childHealthy childDepth childRank) old hh depth hr
  exact hall (I.stageCount - next) next rfl old hh depth hr

end PaperProofs.Retained.PRetObservationEnvelope119
