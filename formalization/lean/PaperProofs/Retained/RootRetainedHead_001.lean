module

public import PaperProofs.Retained.RootRetainedAsymp_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics
open scoped Topology ENNReal

namespace RootRetainedHead

open PaperProofs.Common PaperProofs.Retained PaperProofs.Statistics
open PaperProofs.Retained.PRetFreshLocalPrices042
open RootRetainedAsymp

variable {I : Instance}

theorem healthy_empty (next : ℕ) (hn : next ≤ I.stageCount) : Healthy I next ∅ :=
  ⟨hn, Finset.empty_subset _, matchable_empty I⟩

theorem girth_le_rank_empty (later : List I.Stage) : girth I ≤ errorRank I later ∅ := by
  apply le_of_not_gt
  intro hlt
  obtain ⟨budget, hb⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  obtain ⟨errors, _, hcard, hbad⟩ :=
    (rank_le_nat_iff_future_set I later ∅ budget).mp hb.symm.le
  have hbad' : ¬ Matchable I errors := by simpa only [Finset.empty_union] using hbad
  have hg := (girth_le_card_of_unmatchable hbad').trans (ENat.natCast_le_natCast.mpr hcard)
  rw [hb] at hg
  exact (not_le_of_gt hlt) hg

noncomputable def localTerm (input : StatisticalInput I) (stage : I.Stage) (penalty : ℝ) : ℝ :=
  (input.experiment stage).localValueReal
    (badPenaltyReal input stage ∅ penalty - goodPenaltyReal input stage ∅ penalty)

theorem zero_scale_of_higher (f : ℝ → ℝ) (depth higher : ℕ) (hle : depth ≤ higher)
    (hf : Tendsto (fun penalty => f penalty / iteratedLog higher penalty) atTop (𝓝 0)) :
    Tendsto (fun penalty => f penalty / iteratedLog depth penalty) atTop (𝓝 0) := by
  by_cases he : higher = depth
  · simpa only [he] using hf
  · have hratio := iteratedLog_div_tendsto_zero_of_lt depth higher (by omega)
    have hp : Tendsto (fun penalty => (f penalty / iteratedLog higher penalty) *
        (iteratedLog higher penalty / iteratedLog depth penalty)) atTop (𝓝 0) := by
      simpa only [zero_mul] using hf.mul hratio
    apply hp.congr'
    filter_upwards [(iteratedLog_tendsto_atTop depth).eventually_ne_atTop 0,
      (iteratedLog_tendsto_atTop higher).eventually_ne_atTop 0] with penalty hd hh
    field_simp [hd, hh]

theorem badReal_zero_of_top (input : StatisticalInput I) (stage : I.Stage)
    (ht : errorRank I (stagesFrom I (stage.val + 1)) (insert stage ∅) = ⊤)
    (penalty : ℝ) : badPenaltyReal input stage ∅ penalty = 0 := by
  classical
  have hm : Matchable I (insert stage ∅) := by
    by_contra hbad
    have hz := rank_zero_of_unmatchable (stagesFrom I (stage.val + 1)) (insert stage ∅) hbad
    rw [ht] at hz
    exact ENat.top_ne_natCast 0 hz
  simp only [badPenaltyReal, hm, ite_true, freshReal_zero_of_top input _ _ ht penalty]

theorem local_zero_of_bad_top (input : StatisticalInput I) (stage : I.Stage)
    (ht : errorRank I (stagesFrom I (stage.val + 1)) (insert stage ∅) = ⊤)
    (penalty : ℝ) (hp : 0 ≤ penalty) : localTerm input stage penalty = 0 := by
  have hb := badReal_zero_of_top input stage ht penalty
  have hg : goodPenaltyReal input stage ∅ penalty = 0 :=
    le_antisymm ((goodPenalty_le_badPenalty input stage ∅ penalty hp).trans_eq hb)
      (goodPenalty_nonneg input stage ∅ penalty)
  unfold localTerm
  rw [hb, hg, sub_self]
  exact le_antisymm ((input.experiment stage).localValueReal_le 0 le_rfl)
    ((input.experiment stage).localValueReal_nonneg 0)

theorem local_head_scale (input : StatisticalInput I) (hrec : FreshPenaltyRecursion input)
    (depth : ℕ) (hgirth : girth I = (depth : ℕ∞)) (stage : I.Stage) :
    Tendsto (fun penalty => localTerm input stage penalty / iteratedLog depth penalty)
      atTop (𝓝 (if stage ∈ girthHeads I then (input.experiment stage).coefficient else 0)) := by
  classical
  have hdepth : 0 < depth := by
    have h := one_le_girth I
    rw [hgirth] at h
    exact ENat.natCast_le_natCast.mp h
  have hh := healthy_empty stage.val stage.isLt.le
  have ih := finiteLeading_all input hrec (stage.val + 1)
  by_cases hhead : stage ∈ girthHeads I
  · rw [ite_eq_left hhead]
    have hbadRank : errorRank I (stagesFrom I (stage.val + 1)) (insert stage ∅) =
        ((depth - 1 : ℕ) : ℕ∞) := by
      simpa only [Finset.insert_empty] using (bad_successor_rank_iff_girthHead I stage depth hgirth).mpr hhead
    obtain ⟨B, hB, hbad⟩ := bad_leading input stage ih ∅ hh (depth - 1) hbadRank
    have hgoodHigher : ((depth - 1 : ℕ) : ℕ∞) < errorRank I (stagesFrom I (stage.val + 1)) ∅ := by
      apply lt_of_lt_of_le _ (hgirth ▸ girth_le_rank_empty (stagesFrom I (stage.val + 1)))
      exact ENat.natCast_lt_natCast.mpr (by omega)
    have hgood := good_scale_zero input stage ih ∅ hh (depth - 1) hgoodHigher
    have hgap : Tendsto (fun penalty =>
        (badPenaltyReal input stage ∅ penalty - goodPenaltyReal input stage ∅ penalty) /
          iteratedLog (depth - 1) penalty) atTop (𝓝 B) := by
      simpa only [sub_div, sub_zero] using hbad.sub hgood
    have hlocal := (input.experiment stage).localValueReal_iteratedLog_succ_of_tendsto
      (fun penalty => badPenaltyReal input stage ∅ penalty - goodPenaltyReal input stage ∅ penalty)
      (depth - 1) B hB hgap
    simpa only [localTerm, Nat.sub_add_cancel hdepth] using
      healthyLeading_unnormalize (localTerm input stage) ((depth - 1) + 1)
        (input.experiment stage).coefficient (input.experiment stage).coefficient_pos.ne' hlocal
  · rw [ite_eq_right hhead]
    by_cases ht : errorRank I (stagesFrom I (stage.val + 1)) (insert stage ∅) = ⊤
    · apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)).congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with penalty hp
      rw [local_zero_of_bad_top input stage ht penalty hp, zero_div]
    · obtain ⟨badDepth, hb⟩ := ENat.ne_top_iff_exists.mp ht
      have hle : depth ≤ badDepth + 1 := by
        have h := (hgirth ▸ girth_le_rank_empty (stagesFrom I stage.val)).trans
          (show errorRank I (stagesFrom I stage.val) ∅ ≤
            1 + errorRank I (stagesFrom I (stage.val + 1)) (insert stage ∅) from by
              rw [rank_suffix_step stage ∅ hh]; exact min_le_right _ _)
        rw [← hb] at h
        exact ENat.natCast_le_natCast.mp (by
          simpa only [ENat.natCast_add, ENat.natCast_one, add_comm] using h)
      have hne : badDepth ≠ depth - 1 := by
        intro he
        apply hhead
        apply (bad_successor_rank_iff_girthHead I stage depth hgirth).mp
        simpa only [Finset.insert_empty, he] using hb.symm
      obtain ⟨B, hB, hbad⟩ := bad_leading input stage ih ∅ hh badDepth hb.symm
      exact zero_scale_of_higher (localTerm input stage) depth badDepth (by omega)
        (local_negligible input stage ∅ badDepth B hB hbad)

end RootRetainedHead
