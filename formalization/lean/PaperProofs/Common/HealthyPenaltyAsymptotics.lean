module

public import PaperProofs.Common.NativeBellmanValueUpper
public import PaperProofs.Common.HealthyInfiniteRank
public import PaperProofs.Common.PenaltyAsymptotics
public import PaperProofs.Statistics.IteratedLogComparison
public import PaperProofs.Common.HealthySuffixStep
public import PaperProofs.Statistics.LocalIteratedComposition
public import PaperProofs.Common.HealthyBadMinimum

/-! Fixed-input strict-suffix induction for the original independent healthy
penalty value. Current-stage cancellation consumes only a positive bad-child
leading term obtained from strictly shorter suffixes. -/

@[expose] public section

open Filter Asymptotics
open scoped Topology ENNReal

namespace PaperProofs.Common

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

def HealthyFiniteLeading (input : StatisticalInput I) (next : ℕ) : Prop :=
  ∀ (available : Finset I.Tool) (depth : ℕ),
    errorRank (I.compatibility.drop next) available = (depth : ℕ∞) →
      0 < depth ∧ 0 < input.suffixCoefficient next available ∧
        Tendsto (fun price : ℝ => input.healthyPenaltyReal next available price /
          (input.suffixCoefficient next available * iteratedLog depth price)) atTop (𝓝 1)

theorem healthyLeading_unnormalize (f : ℝ → ℝ) (depth : ℕ) (C : ℝ) (hC : C ≠ 0)
    (hf : Tendsto (fun price => f price / (C * iteratedLog depth price)) atTop (𝓝 1)) :
    Tendsto (fun price => f price / iteratedLog depth price) atTop (𝓝 C) := by
  have hp : Tendsto (fun price => (f price / (C * iteratedLog depth price)) * C) atTop (𝓝 C) := by
    simpa only [one_mul] using hf.mul_const C
  apply hp.congr'
  filter_upwards [(iteratedLog_tendsto_atTop depth).eventually_ne_atTop 0] with price hs
  field_simp [hC, hs]

theorem healthyLeading_normalize (f : ℝ → ℝ) (depth : ℕ) (C : ℝ) (hC : C ≠ 0)
    (hf : Tendsto (fun price => f price / iteratedLog depth price) atTop (𝓝 C)) :
    Tendsto (fun price => f price / (C * iteratedLog depth price)) atTop (𝓝 1) := by
  have hp := hf.div_const C
  simpa only [div_div, mul_comm (iteratedLog depth _) C, div_self hC] using hp

theorem healthyLeading_higher_negligible (f : ℝ → ℝ) (depth higher : ℕ) (hlt : depth < higher)
    (C : ℝ) (hC : C ≠ 0)
    (hf : Tendsto (fun price => f price / (C * iteratedLog higher price)) atTop (𝓝 1)) :
    Tendsto (fun price => f price / iteratedLog depth price) atTop (𝓝 0) := by
  have hp : Tendsto (fun price => (f price / iteratedLog higher price) *
      (iteratedLog higher price / iteratedLog depth price)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (healthyLeading_unnormalize f higher C hC hf).mul
      (iteratedLog_div_tendsto_zero_of_lt depth higher hlt)
  apply hp.congr'
  filter_upwards [(iteratedLog_tendsto_atTop depth).eventually_ne_atTop 0,
    (iteratedLog_tendsto_atTop higher).eventually_ne_atTop 0] with price hd hh
  field_simp [hd, hh]

theorem healthyGood_scale_of_shorter (input : StatisticalInput I) (stage : I.Stage)
    (ih : HealthyFiniteLeading input (stage.val + 1)) (available : Finset I.Tool)
    (depth : ℕ) (horder : (depth : ℕ∞) ≤ errorRank (I.compatibility.drop (stage.val + 1)) available) :
    Tendsto (fun price => input.goodPenaltyReal stage available price / iteratedLog depth price)
      atTop (𝓝 (if errorRank (I.compatibility.drop (stage.val + 1)) available = (depth : ℕ∞)
        then input.suffixCoefficient (stage.val + 1) available else 0)) := by
  classical
  by_cases htop : errorRank (I.compatibility.drop (stage.val + 1)) available = ⊤
  · have hf : input.goodPenaltyReal stage available = fun _ => 0 := by
      funext price
      exact input.healthyPenaltyReal_zero_of_infiniteRank (stage.val + 1) available htop price
    simp only [hf, zero_div]
    simpa only [htop, ENat.top_ne_natCast, ite_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  · obtain ⟨higher, hhigher⟩ := ENat.ne_top_iff_exists.mp htop
    have hd : depth ≤ higher := ENat.natCast_le_natCast.mp (hhigher ▸ horder)
    obtain ⟨_, hC, hlim⟩ := ih available higher hhigher.symm
    by_cases heq : higher = depth
    · subst higher
      simpa only [← hhigher, ite_true, StatisticalInput.goodPenaltyReal] using
        healthyLeading_unnormalize (input.healthyPenaltyReal (stage.val + 1) available) depth
          (input.suffixCoefficient (stage.val + 1) available) hC.ne' hlim
    · have hlim0 := healthyLeading_higher_negligible (input.healthyPenaltyReal (stage.val + 1) available)
        depth higher (by omega) (input.suffixCoefficient (stage.val + 1) available) hC.ne' hlim
      simpa only [← hhigher, ENat.natCast_inj, heq, ite_false, StatisticalInput.goodPenaltyReal] using hlim0

theorem healthyBad_noTool_leading (input : StatisticalInput I) (stage : I.Stage)
    (available : Finset I.Tool) (hempty : ¬(I.eligible stage ∩ available).Nonempty) :
    Tendsto (fun price : ℝ => input.badPenaltyReal stage available price / iteratedLog 0 price)
      atTop (𝓝 1) := by
  classical
  have hvalue : input.badPenaltyReal stage available = fun price => price := by
    funext price
    simp only [StatisticalInput.badPenaltyReal, hempty, ↓reduceDIte]
  apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with price hp
  simp only [hvalue, iteratedLog, div_self hp.ne']

theorem healthyLocal_scale_of_bad_leading (input : StatisticalInput I) (stage : I.Stage)
    (ih : HealthyFiniteLeading input (stage.val + 1)) (available : Finset I.Tool)
    (depth badDepth : ℕ)
    (hrank : errorRank (I.compatibility.drop stage.val) available = (depth : ℕ∞))
    (hbadRank : badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available = (badDepth : ℕ∞))
    (B : ℝ) (hB : 0 < B)
    (hbad : Tendsto (fun price : ℝ => input.badPenaltyReal stage available price /
      iteratedLog badDepth price) atTop (𝓝 B)) :
    Tendsto (fun price : ℝ => (input.experiment stage).localValueReal
        (input.badPenaltyReal stage available price - input.goodPenaltyReal stage available price) /
          iteratedLog depth price) atTop
      (𝓝 (if badDepth + 1 = depth then (input.experiment stage).coefficient else 0)) := by
  have hgoodOrder : (depth : ℕ∞) ≤ errorRank (I.compatibility.drop (stage.val + 1)) available := by
    rw [← hrank, I.errorRank_suffix_step stage available]
    exact min_le_left _ _
  have hbadGood := badChildRank_le_goodRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available
  rw [hbadRank] at hbadGood
  have hbadOrder : (badDepth : ℕ∞) ≤ (depth : ℕ∞) := by
    rw [← hrank, I.errorRank_suffix_step stage available, hbadRank]
    exact le_min hbadGood (by simpa only [add_comm] using (le_add_of_nonneg_right (show (0 : ℕ∞) ≤ 1 from bot_le) :
      (badDepth : ℕ∞) ≤ (badDepth : ℕ∞) + 1))
  have hdepthUpper : depth ≤ badDepth + 1 := by
    have hb : (depth : ℕ∞) ≤ 1 + (badDepth : ℕ∞) := by
      rw [← hrank, I.errorRank_suffix_step stage available, hbadRank]
      exact min_le_right _ _
    exact ENat.natCast_le_natCast.mp (by simpa only [ENat.natCast_add, ENat.natCast_one, add_comm] using hb)
  have hbadLower : badDepth ≤ depth := ENat.natCast_le_natCast.mp hbadOrder
  by_cases heq : badDepth + 1 = depth
  · have hgoodNe : errorRank (I.compatibility.drop (stage.val + 1)) available ≠ (badDepth : ℕ∞) := by
      intro hg
      rw [hg] at hgoodOrder
      have hh : depth ≤ badDepth := ENat.natCast_le_natCast.mp hgoodOrder
      omega
    have hgood0 := healthyGood_scale_of_shorter input stage ih available badDepth hbadGood
    simp only [hgoodNe, ite_false] at hgood0
    have hgap : Tendsto (fun price : ℝ =>
        (input.badPenaltyReal stage available price - input.goodPenaltyReal stage available price) /
          iteratedLog badDepth price) atTop (𝓝 B) := by
      simpa only [sub_div, sub_zero] using hbad.sub hgood0
    have hj := (input.experiment stage).localValueReal_iteratedLog_succ_of_tendsto
      (fun price => input.badPenaltyReal stage available price - input.goodPenaltyReal stage available price)
      badDepth B hB hgap
    simpa only [heq, ite_true] using healthyLeading_unnormalize
      (fun price => (input.experiment stage).localValueReal
        (input.badPenaltyReal stage available price - input.goodPenaltyReal stage available price))
      (badDepth + 1) (input.experiment stage).coefficient (input.experiment stage).coefficient_pos.ne' hj
  · have hd : depth = badDepth := by omega
    rw [ite_eq_right heq]
    simpa only [hd] using
      input.equalRankLocalTerm_tendsto_zero_of_bad_leading stage available badDepth B hB hbad

theorem healthyBad_leading_of_shorter (input : StatisticalInput I) (stage : I.Stage)
    (ih : HealthyFiniteLeading input (stage.val + 1)) (available : Finset I.Tool)
    (badDepth : ℕ)
    (hbadRank : badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available = (badDepth : ℕ∞)) :
    ∃ B : ℝ, 0 < B ∧ Tendsto (fun price : ℝ => input.badPenaltyReal stage available price /
      iteratedLog badDepth price) atTop (𝓝 B) := by
  classical
  by_cases hnonempty : (I.eligible stage ∩ available).Nonempty
  · exact input.badPenaltyReal_leading_of_shorter stage available badDepth hnonempty hbadRank ih
  · have hzero : badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available = 0 :=
      (badChildRank_eq_zero_iff _ _ _).mpr (Finset.not_nonempty_iff_eq_empty.mp hnonempty)
    have hb : badDepth = 0 := by exact_mod_cast (hbadRank.symm.trans hzero)
    subst badDepth
    exact ⟨1, zero_lt_one, healthyBad_noTool_leading input stage available hnonempty⟩

theorem healthyPenalty_finite_step (input : StatisticalInput I) (stage : I.Stage)
    (ih : HealthyFiniteLeading input (stage.val + 1)) : HealthyFiniteLeading input stage.val := by
  intro available depth hrank
  have hfinite : errorRank (I.compatibility.drop stage.val) available ≠ ⊤ := by
    rw [hrank]
    exact ENat.natCast_ne_top depth
  have hdepth : 0 < depth := by
    have hp := errorRank_pos (I.compatibility.drop stage.val) available
    rw [hrank] at hp
    exact_mod_cast hp
  have hC := input.suffixCoefficient_pos stage.val available hfinite
  obtain ⟨badDepth, hbadDepth⟩ := ENat.ne_top_iff_exists.mp (I.badChildRank_suffix_ne_top stage available hfinite)
  obtain ⟨B, hB, hbad⟩ := healthyBad_leading_of_shorter input stage ih available badDepth hbadDepth.symm
  have hgoodOrder : (depth : ℕ∞) ≤ errorRank (I.compatibility.drop (stage.val + 1)) available := by
    rw [← hrank, I.errorRank_suffix_step stage available]
    exact min_le_left _ _
  have hgood := healthyGood_scale_of_shorter input stage ih available depth hgoodOrder
  have hlocal := healthyLocal_scale_of_bad_leading input stage ih available depth badDepth hrank hbadDepth.symm B hB hbad
  have hcoefficient := input.suffixCoefficient_step stage available hfinite
  rw [hrank, ← hbadDepth, ← ENat.natCast_one, ← ENat.natCast_add] at hcoefficient
  simp only [ENat.natCast_inj] at hcoefficient
  let bracket : ℝ → ℝ := fun price => input.goodPenaltyReal stage available price +
    (input.experiment stage).localValueReal
      (input.badPenaltyReal stage available price - input.goodPenaltyReal stage available price)
  have hbracket : Tendsto (fun price => bracket price / iteratedLog depth price) atTop
      (𝓝 (input.suffixCoefficient stage.val available)) := by
    simpa only [bracket, ← add_div, hcoefficient] using hgood.add hlocal
  have hmin := min_id_iteratedLog_tendsto_of_leading bracket depth (by omega)
    (input.suffixCoefficient stage.val available) hbracket
  have hvalue : input.healthyPenaltyReal stage.val available =ᶠ[atTop] fun price => min price (bracket price) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with price hp
    exact Native.currentPenaltyRecursion input stage available price hp
  have hscale : Tendsto (fun price => input.healthyPenaltyReal stage.val available price /
      iteratedLog depth price) atTop (𝓝 (input.suffixCoefficient stage.val available)) := by
    apply hmin.congr'
    filter_upwards [hvalue] with price hp
    rw [hp]
  exact ⟨hdepth, hC, healthyLeading_normalize (input.healthyPenaltyReal stage.val available)
    depth (input.suffixCoefficient stage.val available) hC.ne' hscale⟩

theorem healthyFiniteLeading_all (input : StatisticalInput I) : ∀ next : ℕ, HealthyFiniteLeading input next := by
  have hall : ∀ size : ℕ, ∀ next : ℕ, I.stageCount - next = size → HealthyFiniteLeading input next := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro next hsize
      by_cases hlive : next < I.stageCount
      · let stage : I.Stage := ⟨next, hlive⟩
        have hshort : I.stageCount - (next + 1) < size := by omega
        exact healthyPenalty_finite_step input stage (ih _ hshort (next + 1) rfl)
      · intro available depth hrank
        have hnil : I.compatibility.drop next = [] := List.drop_eq_nil_of_le (by
          change I.stageCount ≤ next
          omega)
        rw [hnil, errorRank_terminal] at hrank
        exact (ENat.top_ne_natCast depth hrank).elim
  intro next
  exact hall (I.stageCount - next) next rfl

theorem StatisticalInput.penaltyAsymptotics (input : StatisticalInput I) : input.PenaltyAsymptotics := by
  intro next available
  refine ⟨?_, (healthyFiniteLeading_all input next) available⟩
  intro htop price _
  exact input.healthyPenalty_zero_of_infiniteRank next available htop (ENNReal.ofReal price)

theorem StatisticalInput.equalRankCancellation (input : StatisticalInput I) : input.EqualRankCancellation := by
  intro stage available depth _ _ hbadRank
  obtain ⟨B, hB, hbad⟩ := healthyBad_leading_of_shorter input stage
    (healthyFiniteLeading_all input (stage.val + 1)) available depth hbadRank
  exact input.equalRankLocalTerm_isLittleO_of_bad_leading stage available depth B hB hbad

end PaperProofs.Common
