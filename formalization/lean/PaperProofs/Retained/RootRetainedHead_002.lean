module

public import PaperProofs.Retained.RootRetainedHead_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter Asymptotics
open scoped Topology ENNReal BigOperators

namespace RootRetainedHead

open PaperProofs.Common PaperProofs.Retained PaperProofs.Statistics
open PaperProofs.Retained.PRetFreshInfiniteBoundary044

variable {I : Instance}

noncomputable def suffixCoefficient (input : StatisticalInput I) (next : ℕ) : ℝ :=
  ∑ stage ∈ girthHeads I, if next ≤ stage.val then (input.experiment stage).coefficient else 0

theorem suffixCoefficient_zero (input : StatisticalInput I) : suffixCoefficient input 0 = headCoefficient input := by
  simp only [suffixCoefficient, Nat.zero_le, ite_true, headCoefficient]

theorem suffixCoefficient_past_end (input : StatisticalInput I) (next : ℕ) (hn : I.stageCount ≤ next) :
    suffixCoefficient input next = 0 := by
  apply Finset.sum_eq_zero
  intro stage _
  exact ite_eq_right (fun h => (Nat.not_lt_of_ge (hn.trans h)) stage.isLt)

theorem suffixCoefficient_step (input : StatisticalInput I) (stage : I.Stage) :
    suffixCoefficient input stage.val =
      (if stage ∈ girthHeads I then (input.experiment stage).coefficient else 0) +
        suffixCoefficient input (stage.val + 1) := by
  classical
  have hsplit (i : I.Stage) :
      (if stage.val ≤ i.val then (input.experiment i).coefficient else 0) =
        (if i = stage then (input.experiment i).coefficient else 0) +
          (if stage.val + 1 ≤ i.val then (input.experiment i).coefficient else 0) := by
    by_cases he : i = stage
    · subst i
      simp
    · have hne : i.val ≠ stage.val := fun h => he (Fin.ext h)
      by_cases hl : stage.val + 1 ≤ i.val
      · simp only [Nat.le_of_succ_le hl, hl, ite_true, he, ite_false, zero_add]
      · have hn : ¬ stage.val ≤ i.val := by omega
        simp only [hl, hn, he, ite_false, zero_add]
  unfold suffixCoefficient
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  congr 1
  simp

theorem allCorrect_leading (input : StatisticalInput I) (hrec : FreshPenaltyRecursion input)
    (depth : ℕ) (hg : girth I = (depth : ℕ∞)) :
    ∀ next : ℕ, Tendsto (fun penalty => freshPenaltyReal input next ∅ penalty / iteratedLog depth penalty)
      atTop (𝓝 (suffixCoefficient input next)) := by
  have hdepth : 1 ≤ depth := by
    have h := one_le_girth I
    rw [hg] at h
    exact ENat.natCast_le_natCast.mp h
  have hall : ∀ size : ℕ, ∀ next : ℕ, I.stageCount - next = size →
      Tendsto (fun penalty => freshPenaltyReal input next ∅ penalty / iteratedLog depth penalty)
        atTop (𝓝 (suffixCoefficient input next)) := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro next hs
      by_cases hlive : next < I.stageCount
      · let stage : I.Stage := ⟨next, hlive⟩
        have hgood := ih (I.stageCount - (next + 1)) (by omega) (next + 1) rfl
        have hlocal := local_head_scale input hrec depth hg stage
        let bracket : ℝ → ℝ := fun penalty => goodPenaltyReal input stage ∅ penalty + localTerm input stage penalty
        have hbracket : Tendsto (fun penalty => bracket penalty / iteratedLog depth penalty)
            atTop (𝓝 (suffixCoefficient input next)) := by
          have hsum := hgood.add hlocal
          have hc : suffixCoefficient input next = suffixCoefficient input (next + 1) +
              (if stage ∈ girthHeads I then (input.experiment stage).coefficient else 0) := by
            rw [show next = stage.val from rfl, suffixCoefficient_step input stage]
            exact add_comm _ _
          simpa only [bracket, goodPenaltyReal, add_div, hc] using hsum
        have hmin := min_id_iteratedLog_tendsto_of_leading bracket depth hdepth
          (suffixCoefficient input next) hbracket
        apply hmin.congr'
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with penalty hp
        rw [hrec stage ∅ (healthy_empty next hlive.le) penalty hp]
        rfl
      · have hn : I.stageCount ≤ next := by omega
        rw [suffixCoefficient_past_end input next hn]
        apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)).congr'
        exact Filter.Eventually.of_forall (fun penalty => by
          simp only [freshPenaltyReal,
            (freshPenaltyBoundaryClaims input).2.1 next ∅ (ENNReal.ofReal penalty) hn (matchable_empty I),
            ENNReal.toReal_zero, zero_div])
  intro next
  exact hall (I.stageCount - next) next rfl

theorem head_leading (input : StatisticalInput I) (hrec : FreshPenaltyRecursion input)
    (depth : ℕ) (hg : girth I = (depth : ℕ∞)) :
    Tendsto (fun penalty => freshPenaltyReal input 0 ∅ penalty /
      (headCoefficient input * iteratedLog depth penalty)) atTop (𝓝 1) := by
  have hp := headCoefficient_pos input (by rw [hg]; exact ENat.natCast_ne_top depth)
  apply healthyLeading_normalize (freshPenaltyReal input 0 ∅) depth (headCoefficient input) hp.ne'
  simpa only [suffixCoefficient_zero] using allCorrect_leading input hrec depth hg 0

end RootRetainedHead
