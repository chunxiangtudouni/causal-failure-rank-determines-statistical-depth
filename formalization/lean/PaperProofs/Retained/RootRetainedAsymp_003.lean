module

public import PaperProofs.Retained.RootRetainedAsymp_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics
open scoped Topology ENNReal

namespace RootRetainedAsymp

open PaperProofs.Common PaperProofs.Retained PaperProofs.Statistics

variable {I : Instance}

theorem finite_step (input : StatisticalInput I) (hrec : FreshPenaltyRecursion input)
    (stage : I.Stage) (ih : FiniteLeading input (stage.val + 1)) :
    FiniteLeading input stage.val := by
  intro old hh depth hrank
  have hdepth : 0 < depth := by
    have hp := rank_positive (stagesFrom I stage.val) old hh.2.2
    rw [hrank] at hp
    exact_mod_cast hp
  have hfinite : errorRank I (stagesFrom I stage.val) old ≠ ⊤ := by
    rw [hrank]
    exact ENat.natCast_ne_top depth
  have hbad_le := rank_bad_le_current stage old hh
  obtain ⟨badDepth, hbadDepth⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top hfinite hbad_le)
  have hb : badDepth ≤ depth := ENat.natCast_le_natCast.mp (by rwa [← hbadDepth, hrank] at hbad_le)
  have hd : depth ≤ badDepth + 1 := by
    have hle : (depth : ℕ∞) ≤ 1 + (badDepth : ℕ∞) := by
      rw [← hrank, rank_suffix_step stage old hh, ← hbadDepth]
      exact min_le_right _ _
    exact ENat.natCast_le_natCast.mp (by
      simpa only [ENat.natCast_add, ENat.natCast_one, add_comm] using hle)
  have hgOrder : (depth : ℕ∞) ≤ errorRank I (stagesFrom I (stage.val + 1)) old := by
    rw [← hrank, rank_suffix_step stage old hh]
    exact min_le_left _ _
  obtain ⟨G, hG, hGpos, _, hgood⟩ := good_scale input stage ih old hh depth hgOrder
  obtain ⟨B, hB, hbad⟩ := bad_leading input stage ih old hh badDepth hbadDepth.symm
  let localTerm : ℝ → ℝ := fun penalty => (input.experiment stage).localValueReal
    (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty)
  have hlocal : ∃ A : ℝ, 0 ≤ A ∧ 0 < G + A ∧
      Tendsto (fun penalty => localTerm penalty / iteratedLog depth penalty) atTop (𝓝 A) := by
    by_cases hcritical : badDepth + 1 = depth
    · have hgoodHigher : (badDepth : ℕ∞) < errorRank I (stagesFrom I (stage.val + 1)) old := by
        apply lt_of_lt_of_le _ hgOrder
        exact_mod_cast (show badDepth < depth by omega)
      have hgoodZero := good_scale_zero input stage ih old hh badDepth hgoodHigher
      have hgap : Tendsto (fun penalty : ℝ =>
          (badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty) /
            iteratedLog badDepth penalty) atTop (𝓝 B) := by
        simpa only [sub_div, sub_zero] using hbad.sub hgoodZero
      have hlog := (input.experiment stage).localValueReal_iteratedLog_succ_of_tendsto
        (fun penalty => badPenaltyReal input stage old penalty - goodPenaltyReal input stage old penalty)
        badDepth B hB hgap
      refine ⟨(input.experiment stage).coefficient, (input.experiment stage).coefficient_pos.le,
        add_pos_of_nonneg_of_pos hG (input.experiment stage).coefficient_pos, ?_⟩
      simpa only [localTerm, hcritical] using healthyLeading_unnormalize
        localTerm (badDepth + 1) (input.experiment stage).coefficient
        (input.experiment stage).coefficient_pos.ne' hlog
    · have he : depth = badDepth := by omega
      have hgEq : errorRank I (stagesFrom I (stage.val + 1)) old = (depth : ℕ∞) := by
        apply le_antisymm _ hgOrder
        by_contra hnot
        have hright : (depth : ℕ∞) < 1 + (badDepth : ℕ∞) := by
          rw [he, add_comm]
          exact ENat.natCast_lt_succ
        have hlt := lt_min (lt_of_not_ge hnot) hright
        rw [hbadDepth, ← rank_suffix_step stage old hh, hrank] at hlt
        exact (lt_irrefl (depth : ℕ∞)) hlt
      refine ⟨0, le_rfl, by simpa only [add_zero] using hGpos hgEq, ?_⟩
      simpa only [localTerm, he] using local_negligible input stage old badDepth B hB hbad
  obtain ⟨A, _, hpositive, hlocal⟩ := hlocal
  let bracket : ℝ → ℝ := fun penalty => goodPenaltyReal input stage old penalty + localTerm penalty
  have hbracket : Tendsto (fun penalty => bracket penalty / iteratedLog depth penalty)
      atTop (𝓝 (G + A)) := by
    simpa only [bracket, add_div] using hgood.add hlocal
  have hmin := min_id_iteratedLog_tendsto_of_leading bracket depth (by omega) (G + A) hbracket
  have hvalue : freshPenaltyReal input stage.val old =ᶠ[atTop] fun penalty => min penalty (bracket penalty) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with penalty hp
    exact hrec stage old hh penalty hp
  have hscale : Tendsto (fun penalty => freshPenaltyReal input stage.val old penalty / iteratedLog depth penalty)
      atTop (𝓝 (G + A)) := by
    apply hmin.congr'
    filter_upwards [hvalue] with penalty hp
    rw [hp]
  exact ⟨hdepth, G + A, hpositive,
    healthyLeading_normalize (freshPenaltyReal input stage.val old) depth (G + A) hpositive.ne' hscale⟩

theorem finiteLeading_all (input : StatisticalInput I) (hrec : FreshPenaltyRecursion input) :
    ∀ next : ℕ, FiniteLeading input next := by
  have hall : ∀ size : ℕ, ∀ next : ℕ, I.stageCount - next = size → FiniteLeading input next := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro next hs
      by_cases hlive : next < I.stageCount
      · let stage : I.Stage := ⟨next, hlive⟩
        exact finite_step input hrec stage (ih (I.stageCount - (next + 1)) (by omega) (next + 1) rfl)
      · intro old hh depth hrank
        have ht := rank_past_end_top next old (by omega) hh.2.2
        exact (ENat.top_ne_natCast depth (ht.symm.trans hrank)).elim
  intro next
  exact hall (I.stageCount - next) next rfl

theorem freshAsymptotics_of_recursion (input : StatisticalInput I) (hrec : FreshPenaltyRecursion input) :
    FreshPenaltyAsymptotics input ∧ EqualRankCancellation input := by
  constructor
  · intro next old hh depth hrank
    obtain ⟨_, C, hC, hf⟩ := finiteLeading_all input hrec next old hh depth hrank
    refine ⟨C, hC, ?_⟩
    apply (isEquivalent_iff_tendsto_one ?_).mpr hf
    exact ((iteratedLog_tendsto_atTop depth).const_mul_atTop hC).eventually_ne_atTop 0
  · intro stage old hh _ depth _ _ hbadRank
    obtain ⟨B, hB, hbad⟩ := bad_leading input stage
      (finiteLeading_all input hrec (stage.val + 1)) old hh depth hbadRank
    exact local_negligible_isLittleO input stage old depth B hB hbad

end RootRetainedAsymp
