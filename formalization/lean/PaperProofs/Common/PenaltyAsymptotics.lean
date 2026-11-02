module

public import PaperProofs.Common.HealthyValue
public import PaperProofs.Statistics.Coefficient
public import PaperProofs.Statistics.PenaltyScales

/-!
Exact remaining global claims in price-proofs.tex:116--154. The values are
the independently defined Native policy infima from HealthyValue, not solutions
of a recurrence. Every limit fixes the input, suffix and available tools first.
The equal-rank estimate below exposes its strict-continuation leading-term
premise. It does not prove that premise or the global penalty asymptotic.
-/

@[expose] public section

open Filter Asymptotics
open scoped Topology ENNReal

namespace PaperProofs.Common

open PaperProofs.Statistics PaperProofs.Structure

noncomputable def StatisticalInput.suffixCoefficient {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool) : ℝ :=
  (input.freshSuffix next).orderedCoefficient available

@[simp] theorem StatisticalInput.suffixCoefficient_zero {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) : input.suffixCoefficient 0 available = input.orderedCoefficient available := rfl

/-- The frozen equal-rank assertion. This is a statement, not an axiom or a
recurrence definition of G. In particular it asserts no lower bound on Gb-Gg. -/
def StatisticalInput.EqualRankCancellation {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ (stage : I.Stage) (available : Finset I.Tool) (depth : ℕ), 1 ≤ depth →
    errorRank (I.compatibility.drop (stage.val + 1)) available = (depth : ℕ∞) →
    badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available = (depth : ℕ∞) →
    (fun penalty : ℝ => (input.experiment stage).localValueReal
      (input.badPenaltyReal stage available penalty - input.goodPenaltyReal stage available penalty))
      =o[atTop] (iteratedLog depth)

/-- The exact fixed-input penalty law in lem:price-penalty-asymptotic. This
retains both infinite-rank zero value and the positive finite-rank coefficient.
The remaining proof must supply the Native/game bridge and backwards induction. -/
def StatisticalInput.PenaltyAsymptotics {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ (next : ℕ) (available : Finset I.Tool),
    (errorRank (I.compatibility.drop next) available = ⊤ →
      ∀ penalty : ℝ, 0 ≤ penalty → input.healthyPenalty next available (ENNReal.ofReal penalty) = 0) ∧
    ∀ depth : ℕ, errorRank (I.compatibility.drop next) available = (depth : ℕ∞) →
      0 < depth ∧ 0 < input.suffixCoefficient next available ∧
        Tendsto (fun penalty : ℝ => input.healthyPenaltyReal next available penalty /
          (input.suffixCoefficient next available * iteratedLog depth penalty)) atTop (𝓝 1)

/-- The equal-rank proof step uses the bad continuation's leading term only.
That premise belongs to the strict-suffix induction; it is not assumed in the
definition of G or smuggled in as a lower bound on the difference. -/
theorem StatisticalInput.equalRankLocalTerm_tendsto_zero_of_bad_leading {I : Instance}
    (input : StatisticalInput I) (stage : I.Stage) (available : Finset I.Tool)
    (depth : ℕ) (B : ℝ) (hB : 0 < B)
    (hbad : Tendsto (fun penalty : ℝ => input.badPenaltyReal stage available penalty /
      iteratedLog depth penalty) atTop (𝓝 B)) :
    Tendsto (fun penalty : ℝ => (input.experiment stage).localValueReal
      (input.badPenaltyReal stage available penalty - input.goodPenaltyReal stage available penalty) /
        iteratedLog depth penalty) atTop (𝓝 0) := by
  apply (input.experiment stage).localValue_iteratedLog_difference_negligible
    (input.goodPenaltyReal stage available) (input.badPenaltyReal stage available) depth B hB hbad
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with penalty hp
  have horder := input.penalty_successor_order stage available penalty hp
  exact ⟨horder.1, horder.2.1⟩

theorem StatisticalInput.equalRankLocalTerm_isLittleO_of_bad_leading {I : Instance}
    (input : StatisticalInput I) (stage : I.Stage) (available : Finset I.Tool)
    (depth : ℕ) (B : ℝ) (hB : 0 < B)
    (hbad : Tendsto (fun penalty : ℝ => input.badPenaltyReal stage available penalty /
      iteratedLog depth penalty) atTop (𝓝 B)) :
    (fun penalty : ℝ => (input.experiment stage).localValueReal
      (input.badPenaltyReal stage available penalty - input.goodPenaltyReal stage available penalty))
        =o[atTop] (iteratedLog depth) := by
  apply (isLittleO_iff_tendsto' ?_).mpr
    (input.equalRankLocalTerm_tendsto_zero_of_bad_leading stage available depth B hB hbad)
  filter_upwards [(iteratedLog_tendsto_atTop depth).eventually_ne_atTop 0] with penalty hp hzero
  exact (hp hzero).elim

/-- The cap-independent lower half of thm:price, in ENNReal so competitors
with infinite cost remain present. The input is fixed before epsilon/delta;
the same bound applies to every current-allocation contract and accounting. -/
def StatisticalInput.NativeLowerPriceLaw {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ depth : ℕ, errorRank I.compatibility I.tools = (depth : ℕ∞) →
    ∀ ε : ℝ, 0 < ε → ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 → ∀ C : Contract I, C.IsCurrentAllocation →
        ∀ accounting : Native.NormalAccounting I,
          ENNReal.ofReal ((1 - ε) * (input.orderedCoefficient I.tools * iteratedLog depth δ⁻¹)) ≤
            Native.value input C .native accounting (ENNReal.ofReal δ)

/-- A genuine conditional lower-bound connection: the premise is a penalty
asymptotic of an independently defined relaxed infimum, not the Native price
conclusion under another name. No resource certificate is required. -/
theorem StatisticalInput.nativeLowerPriceLaw_of_penaltyAsymptotics {I : Instance}
    (input : StatisticalInput I) (hpenalty : input.PenaltyAsymptotics) : input.NativeLowerPriceLaw := by
  intro depth hrank ε hε
  have hrank0 : errorRank (I.compatibility.drop 0) I.tools = (depth : ℕ∞) := by
    simpa only [List.drop_zero] using hrank
  obtain ⟨_, hC, hlim⟩ := (hpenalty 0 I.tools).2 depth hrank0
  simp only [StatisticalInput.suffixCoefficient_zero] at hC hlim
  let scale : ℝ → ℝ := fun penalty => input.orderedCoefficient I.tools * iteratedLog depth penalty
  have hscale : Tendsto scale atTop atTop :=
    Filter.Tendsto.const_mul_atTop hC (iteratedLog_tendsto_atTop depth)
  have hratio : ∀ᶠ penalty in atTop,
      1 - ε / 2 < input.healthyPenaltyReal 0 I.tools penalty / scale penalty :=
    hlim.eventually (lt_mem_nhds (by linarith : 1 - ε / 2 < 1))
  have hbound : ∀ᶠ penalty : ℝ in atTop,
      ENNReal.ofReal ((1 - ε) * scale penalty) ≤
        input.healthyPenalty 0 I.tools (ENNReal.ofReal penalty) - 1 := by
    filter_upwards [hratio, hscale.eventually_gt_atTop 0, hscale.eventually_ge_atTop (2 / ε)]
      with penalty hr hs hlarge
    have hg : (1 - ε / 2) * scale penalty ≤ input.healthyPenaltyReal 0 I.tools penalty :=
      le_of_lt ((lt_div_iff₀ hs).mp hr)
    have htwo : 2 ≤ scale penalty * ε := (div_le_iff₀ hε).mp hlarge
    have hraw : (1 - ε) * scale penalty ≤ input.healthyPenaltyReal 0 I.tools penalty - 1 := by
      nlinarith
    calc
      _ ≤ ENNReal.ofReal (input.healthyPenaltyReal 0 I.tools penalty - 1) := ENNReal.ofReal_le_ofReal hraw
      _ = _ := by
        rw [ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_one]
        exact congrArg (fun value : ℝ≥0∞ => value - 1)
          (ENNReal.ofReal_toReal (input.healthyPenalty_ne_top 0 I.tools ENNReal.ofReal_ne_top))
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp hbound
  let cutoff : ℝ := max 1 threshold + 1
  have hc : 0 < cutoff := by dsimp [cutoff]; linarith [le_max_left (1 : ℝ) threshold]
  refine ⟨1 / cutoff, one_div_pos.mpr hc, ?_⟩
  intro δ hδ hsmall C hcurrent accounting
  have hinv : cutoff ≤ δ⁻¹ := by
    calc
      cutoff = 1 / (1 / cutoff) := by rw [one_div_one_div]
      _ ≤ 1 / δ := one_div_le_one_div_of_le hδ hsmall.le
      _ = _ := one_div δ
  have hthresholdInv : threshold ≤ δ⁻¹ :=
    (show threshold ≤ cutoff by dsimp [cutoff]; linarith [le_max_right (1 : ℝ) threshold]).trans hinv
  have hrelaxed := hthreshold δ⁻¹ hthresholdInv
  have hnative := input.healthyPenalty_initial_value_lower C hcurrent accounting (ENNReal.ofReal δ)
  rw [← ENNReal.ofReal_inv_of_pos hδ] at hnative
  exact hrelaxed.trans hnative

end PaperProofs.Common
