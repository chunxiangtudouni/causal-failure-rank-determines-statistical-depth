module

public import PaperProofs.Retained.PDROC_RetainedEnvelope_004
public import PaperProofs.Retained.RootRetainedHead_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

namespace PaperProofs.Retained.PRetObservationEnvelope119

open Common Common.Native Statistics MeasureTheory Filter
open scoped ENNReal Topology BigOperators
open RootRetainedAsymp RootRetainedHead

variable {I : Instance}

theorem half_precise_upper (f : ℚ → ℝ) (coefficient : ℝ) (depth : ℕ) (hd : 1 ≤ depth)
    (hf : ∀ eta : ℝ, 0 < eta → ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      f risk ≤ (coefficient + eta) * iteratedLog depth (1 / (risk : ℝ)))
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      f (risk / 2) ≤ (coefficient + eta) * iteratedLog depth (1 / (risk : ℝ)) := by
  have hr : Tendsto (fun risk : ℚ =>
      ((coefficient + eta / 2) * iteratedLog depth (1 / ((risk / 2 : ℚ) : ℝ))) /
        iteratedLog depth (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (coefficient + eta / 2)) := by
    simpa only [mul_div_assoc, mul_one] using
      (rationalRisk_iteratedLog_half_div_tendsto_one depth hd).const_mul (coefficient + eta / 2)
  have hn := upper_of_ratio depth _ _ (eta / 2) (by linarith) hr
  filter_upwards [rationalRisk_half_tendsto_zero.eventually (hf (eta / 2) (by linarith)), hn]
    with risk hb hn
  have he : coefficient + eta / 2 + eta / 2 = coefficient + eta := by ring
  exact (hb.trans hn).trans_eq (by rw [he])

theorem suffixCoefficient_nonneg (input : StatisticalInput I) (next : ℕ) :
    0 ≤ suffixCoefficient input next := by
  classical
  unfold suffixCoefficient
  apply Finset.sum_nonneg
  intro stage _
  split_ifs
  · exact (input.experiment stage).coefficient_pos.le
  · exact le_rfl

theorem noTool_bad_rank_zero (stage : I.Stage) (old : Finset I.Stage)
    (hc : rankCase I stage old = some .noTool) :
    errorRank I (stagesFrom I (stage.val + 1)) (insert stage old) = 0 := by
  have hm : ¬ Matchable I (insert stage old) := by
    intro hm
    unfold rankCase at hc
    cases hp : rankIndex I stage.val old with
    | none => rw [hp] at hc; cases hc
    | some depth =>
      rw [hp, ite_eq_right (not_not.mpr hm)] at hc
      cases hq : rankIndex I (stage.val + 1) (insert stage old) with
      | none => rw [hq] at hc; cases hc
      | some j =>
        rw [hq] at hc
        dsimp only at hc
        split_ifs at hc; cases hc
  exact rank_zero_of_unmatchable _ _ hm

theorem finiteBad_head_indicator (input : StatisticalInput I) (depth : ℕ)
    (hg : girth I = (depth : ℕ∞)) (stage : I.Stage) (j : ℕ+)
    (hr : errorRank I (stagesFrom I (stage.val + 1)) (insert stage ∅) = (j.val : ℕ∞)) :
    (input.experiment stage).coefficient * (if depth = j.val + 1 then 1 else 0) =
      if stage ∈ girthHeads I then (input.experiment stage).coefficient else 0 := by
  have hd : 1 ≤ depth := by
    have h := one_le_girth I
    rw [hg] at h
    exact ENat.natCast_le_natCast.mp h
  have he : stage ∈ girthHeads I ↔ depth = j.val + 1 := by
    constructor
    · intro hh
      have hb := (bad_successor_rank_iff_girthHead I stage depth hg).mpr hh
      have hj : j.val = depth - 1 := ENat.natCast_inj.mp (hr.symm.trans (by
        simpa only [Finset.insert_empty] using hb))
      omega
    · intro hj
      apply (bad_successor_rank_iff_girthHead I stage depth hg).mp
      simpa only [Finset.insert_empty, hj, Nat.add_sub_cancel] using hr
  by_cases hh : stage ∈ girthHeads I
  · rw [ite_eq_left hh, ite_eq_left (he.mp hh), mul_one]
  · rw [ite_eq_right hh, ite_eq_right (fun h => hh (he.mpr h)), mul_zero]

theorem observationEnvelope_head_upper (input : StatisticalInput I) (depth : ℕ)
    (hg : girth I = (depth : ℕ∞)) (next : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      observationEnvelopeReal input next ∅ risk ≤
        (suffixCoefficient input next + eta) * iteratedLog depth (1 / (risk : ℝ)) := by
  have hd : 1 ≤ depth := by
    have h := one_le_girth I
    rw [hg] at h
    exact ENat.natCast_le_natCast.mp h
  have hall : ∀ fuel : ℕ, ∀ next : ℕ, I.stageCount - next = fuel →
      ∀ eta : ℝ, 0 < eta → ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
        observationEnvelopeReal input next ∅ risk ≤
          (suffixCoefficient input next + eta) * iteratedLog depth (1 / (risk : ℝ)) := by
    intro fuel
    induction fuel with
    | zero =>
      intro next hf eta heta
      have hn : I.stageCount ≤ next := Nat.sub_eq_zero_iff_le.mp hf
      have hpos := ((iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop).eventually_ge_atTop 0
      filter_upwards [hpos] with risk hp
      simp only [observationEnvelopeReal, observationEnvelope_past_end input next ∅ risk hn,
        ENNReal.toReal_zero, suffixCoefficient_past_end input next hn, zero_add]
      exact mul_nonneg heta.le hp
    | succ fuel ih =>
      intro next hf eta heta
      have hn : next < I.stageCount := by omega
      let stage : I.Stage := ⟨next, hn⟩
      have hh : Healthy I stage.val ∅ := healthy_empty stage.val stage.isLt.le
      have hchild : I.stageCount - (stage.val + 1) = fuel := by dsimp only [stage]; omega
      have hgood : ∀ slack : ℝ, 0 < slack → ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
          observationEnvelopeReal input (stage.val + 1) ∅ (risk / 2) ≤
            (suffixCoefficient input (stage.val + 1) + slack) * iteratedLog depth (1 / (risk : ℝ)) :=
        fun slack hslack => half_precise_upper _ _ depth hd
          (fun childSlack hchildSlack => ih _ hchild childSlack hchildSlack) slack hslack
      by_cases ht : errorRank I (stagesFrom I stage.val) ∅ = ⊤
      · have hp := ((iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop).eventually_ge_atTop 0
        filter_upwards [hp] with risk hp
        change observationEnvelopeReal input stage.val ∅ risk ≤ _
        rw [observationEnvelopeReal, observationEnvelope_zero_of_rank_top input stage.val ∅ risk ht,
          ENNReal.toReal_zero]
        exact mul_nonneg (by linarith [suffixCoefficient_nonneg input next]) hp
      · obtain ⟨parentDepth, hp⟩ := ENat.ne_top_iff_exists.mp ht
        have hdepthParent : depth ≤ parentDepth := ENat.natCast_le_natCast.mp (by
          simpa only [hg, ← hp] using girth_le_rank_empty (I := I) (stagesFrom I stage.val))
        rcases finite_rank_cases stage ∅ hh parentDepth hp.symm with
          ⟨hc, heq⟩ | ⟨j, hc, hhealthy, hbadRank, horder⟩
        · have hdepth : depth = 1 := by omega
          subst depth
          have hhead : stage ∈ girthHeads I :=
            (bad_successor_rank_iff_girthHead I stage 1 hg).mp (by
              simpa only [Finset.insert_empty, Nat.sub_self, ENat.natCast_zero] using noTool_bad_rank_zero stage ∅ hc)
          have hcoef := suffixCoefficient_step input stage
          rw [ite_eq_left hhead] at hcoef
          filter_upwards [localPriceReal_noTool_eventual input stage (eta / 2) (by linarith),
            hgood (eta / 2) (by linarith), self_mem_nhdsWithin,
            rationalRisk_eventually_le_quarter] with risk hl hg' hpositive hquarter
          change observationEnvelopeReal input stage.val ∅ risk ≤ _
          rw [observationEnvelopeReal_noTool input stage ∅ risk ⟨hpositive, hquarter⟩ hc]
          change _ ≤ (suffixCoefficient input stage.val + eta) * _
          rw [hcoef]
          nlinarith
        · have hlocal := localPriceReal_finiteBad_eventual input stage j depth hd
            (hdepthParent.trans horder) (eta / 3) (by linarith)
          obtain ⟨badCoefficient, hbadPositive, hbad⟩ :=
            observationEnvelope_scaleBound input (stage.val + 1) (insert stage ∅) hhealthy j.val hbadRank
          obtain ⟨bound, _hbound, hweighted⟩ := bad_scale_bound _ badCoefficient hbadPositive.le j hbad
          have hsmall := upper_of_ratio depth (fun _ => bound) 0 (eta / 3) (by linarith)
            (tendsto_const_nhds.div_atTop ((iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop))
          have hcoef := suffixCoefficient_step input stage
          have hind := finiteBad_head_indicator input depth hg stage j hbadRank
          filter_upwards [hlocal, hgood (eta / 3) (by linarith), hweighted, hsmall,
            self_mem_nhdsWithin, rationalRisk_eventually_le_quarter] with risk hl hg' hb hB hpositive hquarter
          change observationEnvelopeReal input stage.val ∅ risk ≤ _
          rw [observationEnvelopeReal_finiteBad input stage ∅ risk ⟨hpositive, hquarter⟩ j hc]
          change _ ≤ (suffixCoefficient input stage.val + eta) * _
          rw [hcoef, ← hind]
          simp only [zero_add] at hB
          nlinarith
  exact hall (I.stageCount - next) next rfl eta heta

theorem observationEnvelopeAsymptotics (input : StatisticalInput I) :
    ObservationEnvelopeAsymptotics input := by
  intro depth hg epsilon hepsilon
  have hd : 1 ≤ depth := by
    have h := one_le_girth I
    rw [hg] at h
    exact ENat.natCast_le_natCast.mp h
  have hC : 0 < headCoefficient input := headCoefficient_pos input (by rw [hg]; exact ENat.natCast_ne_top depth)
  have hu : ∀ eta : ℝ, 0 < eta → ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      observationEnvelopeReal input 0 ∅ risk ≤
        (headCoefficient input + eta) * iteratedLog depth (1 / (risk : ℝ)) := by
    intro eta heta
    simpa only [suffixCoefficient_zero] using observationEnvelope_head_upper input depth hg 0 eta heta
  have hh := half_precise_upper _ (headCoefficient input) depth hd hu
    (epsilon * headCoefficient input) (mul_pos hepsilon hC)
  obtain ⟨cutoff, hcutoff, hnum⟩ := rationalEventually_positive_cutoff hh
  refine ⟨cutoff, hcutoff, ?_⟩
  intro budget hbudget hsmall hcut
  have hv : ReferenceBudgetValid (budget / 2) := ⟨by linarith, by linarith⟩
  rw [← ofReal_observationEnvelopeReal input 0 ∅ (budget / 2) hv]
  apply ENNReal.ofReal_le_ofReal
  have hn := hnum budget hbudget hcut
  have he : headCoefficient input + epsilon * headCoefficient input = (1 + epsilon) * headCoefficient input := by ring
  simpa only [he, one_div] using hn

end PaperProofs.Retained.PRetObservationEnvelope119
