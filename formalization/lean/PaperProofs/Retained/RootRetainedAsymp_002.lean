module

public import PaperProofs.Retained.RootRetainedAsymp_001
public import PaperProofs.Retained.PRet_FreshLocalPrices_042
public import PaperProofs.Retained.PRet_FreshInfiniteBoundary_044
public import PaperProofs.Common.HealthyPenaltyAsymptotics
public import PaperProofs.Statistics.PenaltyScales

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics
open scoped Topology ENNReal

namespace RootRetainedAsymp

open PaperProofs.Common PaperProofs.Retained PaperProofs.Statistics
open PaperProofs.Retained.PRetFreshLocalPrices042
open PaperProofs.Retained.PRetFreshInfiniteBoundary044

variable {I : Instance}

def FiniteLeading (input : StatisticalInput I) (next : ℕ) : Prop :=
  ∀ (old : Finset I.Stage), Healthy I next old → ∀ depth : ℕ,
    errorRank I (stagesFrom I next) old = (depth : ℕ∞) →
      0 < depth ∧ ∃ coefficient : ℝ, 0 < coefficient ∧
        Tendsto (fun penalty : ℝ => freshPenaltyReal input next old penalty /
          (coefficient * iteratedLog depth penalty)) atTop (𝓝 1)

theorem freshReal_zero_of_top (input : StatisticalInput I) (next : ℕ) (old : Finset I.Stage)
    (ht : errorRank I (stagesFrom I next) old = ⊤) (penalty : ℝ) :
    freshPenaltyReal input next old penalty = 0 := by
  simp only [freshPenaltyReal, freshPenalty_zero_of_retained_top input next old ht, ENNReal.toReal_zero]

theorem good_scale (input : StatisticalInput I) (stage : I.Stage)
    (ih : FiniteLeading input (stage.val + 1)) (old : Finset I.Stage)
    (hh : Healthy I stage.val old) (depth : ℕ)
    (horder : (depth : ℕ∞) ≤ errorRank I (stagesFrom I (stage.val + 1)) old) :
    ∃ G : ℝ, 0 ≤ G ∧
      (errorRank I (stagesFrom I (stage.val + 1)) old = (depth : ℕ∞) → 0 < G) ∧
      (errorRank I (stagesFrom I (stage.val + 1)) old ≠ (depth : ℕ∞) → G = 0) ∧
      Tendsto (fun penalty : ℝ => goodPenaltyReal input stage old penalty / iteratedLog depth penalty)
        atTop (𝓝 G) := by
  classical
  by_cases ht : errorRank I (stagesFrom I (stage.val + 1)) old = ⊤
  · refine ⟨0, le_rfl, ?_, fun _ => rfl, ?_⟩
    · intro he
      exact (ENat.top_ne_natCast depth (ht.symm.trans he)).elim
    · apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)).congr'
      exact Filter.Eventually.of_forall (fun penalty => by
        simp only [goodPenaltyReal, freshReal_zero_of_top input _ old ht penalty, zero_div])
  · obtain ⟨higher, hg⟩ := ENat.ne_top_iff_exists.mp ht
    have hd : depth ≤ higher := ENat.natCast_le_natCast.mp (hg ▸ horder)
    obtain ⟨_, C, hC, hf⟩ := ih old (healthy_correct I stage old hh) higher hg.symm
    by_cases he : higher = depth
    · subst higher
      refine ⟨C, hC.le, fun _ => hC, ?_, ?_⟩
      · intro hn
        exact (hn hg.symm).elim
      · exact healthyLeading_unnormalize (freshPenaltyReal input (stage.val + 1) old) depth C hC.ne' hf
    · refine ⟨0, le_rfl, ?_, fun _ => rfl, ?_⟩
      · intro heq
        exact he (ENat.natCast_inj.mp (hg.trans heq)) |>.elim
      · exact healthyLeading_higher_negligible (freshPenaltyReal input (stage.val + 1) old)
          depth higher (by omega) C hC.ne' hf

theorem good_scale_zero (input : StatisticalInput I) (stage : I.Stage)
    (ih : FiniteLeading input (stage.val + 1)) (old : Finset I.Stage)
    (hh : Healthy I stage.val old) (depth : ℕ)
    (horder : (depth : ℕ∞) < errorRank I (stagesFrom I (stage.val + 1)) old) :
    Tendsto (fun penalty : ℝ => goodPenaltyReal input stage old penalty / iteratedLog depth penalty)
      atTop (𝓝 0) := by
  obtain ⟨G, _, _, hz, hf⟩ := good_scale input stage ih old hh depth horder.le
  simpa only [hz (ne_of_gt horder)] using hf

theorem bad_leading (input : StatisticalInput I) (stage : I.Stage)
    (ih : FiniteLeading input (stage.val + 1)) (old : Finset I.Stage)
    (hh : Healthy I stage.val old) (depth : ℕ)
    (hr : errorRank I (stagesFrom I (stage.val + 1)) (insert stage old) = (depth : ℕ∞)) :
    ∃ B : ℝ, 0 < B ∧
      Tendsto (fun penalty : ℝ => badPenaltyReal input stage old penalty / iteratedLog depth penalty)
        atTop (𝓝 B) := by
  classical
  by_cases hm : Matchable I (insert stage old)
  · obtain ⟨_, B, hB, hf⟩ := ih (insert stage old) ((healthy_error_iff I stage old hh).mpr hm) depth hr
    refine ⟨B, hB, ?_⟩
    simpa only [badPenaltyReal, hm, ite_true] using
      healthyLeading_unnormalize (freshPenaltyReal input (stage.val + 1) (insert stage old)) depth B hB.ne' hf
  · have hd : depth = 0 := by
      exact_mod_cast hr.symm.trans (rank_zero_of_unmatchable _ (insert stage old) hm)
    subst depth
    refine ⟨1, zero_lt_one, ?_⟩
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with penalty hp
    simp only [badPenaltyReal, hm, ite_false, iteratedLog, div_self hp.ne']

theorem local_negligible (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (depth : ℕ) (B : ℝ) (hB : 0 < B)
    (hbad : Tendsto (fun penalty : ℝ => badPenaltyReal input stage old penalty / iteratedLog depth penalty)
      atTop (𝓝 B)) :
    Tendsto (fun penalty : ℝ => (input.experiment stage).localValueReal
      (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty) /
        iteratedLog depth penalty) atTop (𝓝 0) := by
  apply (input.experiment stage).localValue_iteratedLog_difference_negligible
    (goodPenaltyReal input stage old) (badPenaltyReal input stage old) depth B hB hbad
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with penalty hp
  exact ⟨goodPenalty_nonneg input stage old penalty,
    goodPenalty_le_badPenalty input stage old penalty hp⟩

theorem local_negligible_isLittleO (input : StatisticalInput I) (stage : I.Stage)
    (old : Finset I.Stage) (depth : ℕ) (B : ℝ) (hB : 0 < B)
    (hbad : Tendsto (fun penalty : ℝ => badPenaltyReal input stage old penalty / iteratedLog depth penalty)
      atTop (𝓝 B)) :
    (fun penalty : ℝ => (input.experiment stage).localValueReal
      (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty))
        =o[atTop] iteratedLog depth := by
  apply (isLittleO_iff_tendsto' ?_).mpr (local_negligible input stage old depth B hB hbad)
  filter_upwards [(iteratedLog_tendsto_atTop depth).eventually_ne_atTop 0] with penalty hp hz
  exact (hp hz).elim

end RootRetainedAsymp
