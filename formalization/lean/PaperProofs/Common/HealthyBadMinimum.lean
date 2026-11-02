module

public import PaperProofs.Common.PenaltyAsymptotics
public import PaperProofs.Statistics.IteratedLogComparison
public import Mathlib.Topology.Order.Lattice

/-! Finite bad-successor minima for the independent healthy policy infimum.
The coefficient and maximal-rank set are fixed before the penalty tends to
infinity. No single tool is asserted to minimize every eventual penalty. -/

@[expose] public section

open Filter Asymptotics
open scoped Topology

namespace PaperProofs.Statistics

theorem finiteNatRank_min_leading {Tool : Type*} [DecidableEq Tool]
    (tools : Finset Tool) (htools : tools.Nonempty)
    (rank : Tool → ℕ) (coefficient : Tool → ℝ) (value : Tool → ℝ → ℝ)
    (depth : ℕ) (hbound : ∀ tool ∈ tools, rank tool ≤ depth)
    (hmax : ∃ tool ∈ tools, rank tool = depth)
    (hpositive : ∀ tool ∈ tools, 0 < coefficient tool)
    (hleading : ∀ tool ∈ tools,
      Tendsto (fun price : ℝ => value tool price / iteratedLog (rank tool) price)
        atTop (𝓝 (coefficient tool))) :
    ∃ B : ℝ, 0 < B ∧
      (∃ tool ∈ tools, rank tool = depth ∧ coefficient tool = B) ∧
      (∀ tool ∈ tools, rank tool = depth → B ≤ coefficient tool) ∧
      Tendsto (fun price : ℝ => tools.inf' htools (fun tool => value tool price) /
        iteratedLog depth price) atTop (𝓝 B) := by
  let maximal := tools.filter (fun tool => rank tool = depth)
  obtain ⟨chosen, hchosen, hchosenRank⟩ := hmax
  have hchosenMax : chosen ∈ maximal := Finset.mem_filter.mpr ⟨hchosen, hchosenRank⟩
  have hmaximal : maximal.Nonempty := ⟨chosen, hchosenMax⟩
  let B := maximal.inf' hmaximal coefficient
  have hB : 0 < B := by
    apply (Finset.lt_inf'_iff _).mpr
    intro tool htool
    exact hpositive tool (Finset.mem_filter.mp htool).1
  have hmaxLeading (tool : Tool) (htool : tool ∈ maximal) :
      Tendsto (fun price : ℝ => value tool price / iteratedLog depth price)
        atTop (𝓝 (coefficient tool)) := by
    have hm := Finset.mem_filter.mp htool
    simpa only [hm.2] using hleading tool hm.1
  have hchosenLeading := hmaxLeading chosen hchosenMax
  have hdiscard : ∀ᶠ price : ℝ in atTop, ∀ tool ∈ tools,
      maximal.inf' hmaximal (fun tool => value tool price) ≤ value tool price := by
    apply (Filter.eventually_all_finset tools).mpr
    intro tool htool
    by_cases heq : rank tool = depth
    · exact Filter.Eventually.of_forall (fun _ => Finset.inf'_le _
        (Finset.mem_filter.mpr ⟨htool, heq⟩))
    · have hlt : rank tool < depth := lt_of_le_of_ne (hbound tool htool) heq
      have hzero : Tendsto (fun price : ℝ => value chosen price / iteratedLog (rank tool) price)
          atTop (𝓝 0) := by
        have hp := hchosenLeading.mul (iteratedLog_div_tendsto_zero_of_lt (rank tool) depth hlt)
        apply (show Tendsto (fun price : ℝ =>
          (value chosen price / iteratedLog depth price) *
            (iteratedLog depth price / iteratedLog (rank tool) price)) atTop (𝓝 0)
          from by simpa only [mul_zero] using hp).congr'
        filter_upwards [(iteratedLog_tendsto_atTop depth).eventually_ne_atTop 0,
          (iteratedLog_tendsto_atTop (rank tool)).eventually_ne_atTop 0] with price hd hr
        field_simp [hd, hr]
      have hpos := hpositive tool htool
      have hsmall := hzero.eventually_lt_const (half_pos hpos)
      have hlarge := (hleading tool htool).eventually_const_lt (half_lt_self hpos)
      filter_upwards [hsmall, hlarge,
        (iteratedLog_tendsto_atTop (rank tool)).eventually_gt_atTop 0] with price hs hl hp
      exact (Finset.inf'_le (fun tool => value tool price) hchosenMax).trans
        (le_of_lt ((div_lt_div_iff_of_pos_right hp).mp (hs.trans hl)))
  have hrestrict : ∀ᶠ price : ℝ in atTop,
      tools.inf' htools (fun tool => value tool price) =
        maximal.inf' hmaximal (fun tool => value tool price) := by
    filter_upwards [hdiscard] with price hp
    apply le_antisymm
    · apply Finset.le_inf'
      intro tool htool
      exact Finset.inf'_le _ (Finset.mem_filter.mp htool).1
    · exact Finset.le_inf' _ _ hp
  have hlimit := Filter.Tendsto.finset_inf'_nhds_apply hmaximal hmaxLeading
  have hnormalized : ∀ᶠ price : ℝ in atTop,
      maximal.inf' hmaximal (fun tool => value tool price / iteratedLog depth price) =
        maximal.inf' hmaximal (fun tool => value tool price) / iteratedLog depth price := by
    filter_upwards [(iteratedLog_tendsto_atTop depth).eventually_gt_atTop 0] with price hp
    apply le_antisymm
    · obtain ⟨tool, htool, heq⟩ := Finset.exists_mem_eq_inf' hmaximal (fun tool => value tool price)
      rw [heq]
      exact Finset.inf'_le _ htool
    · apply Finset.le_inf'
      intro tool htool
      exact div_le_div_of_nonneg_right (Finset.inf'_le _ htool) hp.le
  obtain ⟨tool, htool, heq⟩ := Finset.exists_mem_eq_inf' hmaximal coefficient
  refine ⟨B, hB, ⟨tool, (Finset.mem_filter.mp htool).1,
    (Finset.mem_filter.mp htool).2, heq.symm⟩, ?_, ?_⟩
  · intro other hother hrank
    exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨hother, hrank⟩)
  · apply hlimit.congr'
    filter_upwards [hnormalized, hrestrict] with price hn hr
    rw [hn, hr]

end PaperProofs.Statistics

namespace PaperProofs.Common

open PaperProofs.Statistics PaperProofs.Structure

theorem StatisticalInput.badPenaltyReal_leading_minimum_of_shorter {I : Instance}
    (input : StatisticalInput I) (stage : I.Stage) (available : Finset I.Tool)
    (depth : ℕ) (hnonempty : (I.eligible stage ∩ available).Nonempty)
    (hrank : badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available =
      (depth : ℕ∞))
    (hshorter : ∀ (childAvailable : Finset I.Tool) (childDepth : ℕ),
      errorRank (I.compatibility.drop (stage.val + 1)) childAvailable = (childDepth : ℕ∞) →
        0 < childDepth ∧ 0 < input.suffixCoefficient (stage.val + 1) childAvailable ∧
          Tendsto (fun price : ℝ => input.healthyPenaltyReal (stage.val + 1) childAvailable price /
            (input.suffixCoefficient (stage.val + 1) childAvailable * iteratedLog childDepth price))
            atTop (𝓝 1)) :
    ∃ B : ℝ, 0 < B ∧
      (∃ tool ∈ I.eligible stage ∩ available,
        errorRank (I.compatibility.drop (stage.val + 1)) (available.erase tool) = (depth : ℕ∞) ∧
          input.suffixCoefficient (stage.val + 1) (available.erase tool) = B) ∧
      (∀ tool ∈ I.eligible stage ∩ available,
        errorRank (I.compatibility.drop (stage.val + 1)) (available.erase tool) = (depth : ℕ∞) →
          B ≤ input.suffixCoefficient (stage.val + 1) (available.erase tool)) ∧
      Tendsto (fun price : ℝ => input.badPenaltyReal stage available price / iteratedLog depth price)
        atTop (𝓝 B) := by
  classical
  let K := I.eligible stage ∩ available
  let childRank := fun tool : I.Tool => errorRank (I.compatibility.drop (stage.val + 1)) (available.erase tool)
  let rank := fun tool : I.Tool => (childRank tool).toNat
  let coefficient := fun tool : I.Tool => input.suffixCoefficient (stage.val + 1) (available.erase tool)
  let value := fun tool : I.Tool => input.healthyPenaltyReal (stage.val + 1) (available.erase tool)
  have hbound (tool : I.Tool) (htool : tool ∈ K) : childRank tool ≤ (depth : ℕ∞) := by
    exact (childRank_le_badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1))
      available htool).trans_eq hrank
  have hcast (tool : I.Tool) (htool : tool ∈ K) : (rank tool : ℕ∞) = childRank tool := by
    exact ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top depth) (hbound tool htool))
  have hnatBound (tool : I.Tool) (htool : tool ∈ K) : rank tool ≤ depth :=
    ENat.toNat_le_of_le_natCast (hbound tool htool)
  have hnatMax : ∃ tool ∈ K, rank tool = depth := by
    obtain ⟨tool, htool, heq⟩ := exists_maximizing_tool (I.eligible stage)
      (I.compatibility.drop (stage.val + 1)) available hnonempty
    refine ⟨tool, htool, ?_⟩
    change (errorRank (I.compatibility.drop (stage.val + 1)) (available.erase tool)).toNat = depth
    rw [heq, hrank, ENat.toNat_natCast]
  have hchild (tool : I.Tool) (htool : tool ∈ K) :=
    hshorter (available.erase tool) (rank tool) (hcast tool htool).symm
  have hpositive (tool : I.Tool) (htool : tool ∈ K) : 0 < coefficient tool :=
    (hchild tool htool).2.1
  have hleading (tool : I.Tool) (htool : tool ∈ K) :
      Tendsto (fun price : ℝ => value tool price / iteratedLog (rank tool) price)
        atTop (𝓝 (coefficient tool)) := by
    have hc := hpositive tool htool
    have hp := ((hchild tool htool).2.2).mul_const (coefficient tool)
    apply (show Tendsto (fun price : ℝ =>
      (value tool price / (coefficient tool * iteratedLog (rank tool) price)) * coefficient tool)
      atTop (𝓝 (coefficient tool)) from by simpa only [one_mul] using hp).congr'
    filter_upwards [(iteratedLog_tendsto_atTop (rank tool)).eventually_ne_atTop 0] with price hn
    field_simp [hc.ne', hn]
  obtain ⟨B, hB, ⟨tool, htool, htoolRank, htoolCoefficient⟩, hminimum, hlimit⟩ :=
    finiteNatRank_min_leading K hnonempty rank coefficient value depth hnatBound hnatMax hpositive hleading
  refine ⟨B, hB, ⟨tool, htool, ?_, htoolCoefficient⟩, ?_, ?_⟩
  · exact (hcast tool htool).symm.trans (congrArg (fun n : ℕ => (n : ℕ∞)) htoolRank)
  · intro other hother hotherRank
    apply hminimum other hother
    change (errorRank (I.compatibility.drop (stage.val + 1)) (available.erase other)).toNat = depth
    rw [hotherRank, ENat.toNat_natCast]
  · simpa only [StatisticalInput.badPenaltyReal, hnonempty, ↓reduceDIte] using hlimit

theorem StatisticalInput.badPenaltyReal_leading_of_shorter {I : Instance}
    (input : StatisticalInput I) (stage : I.Stage) (available : Finset I.Tool)
    (depth : ℕ) (hnonempty : (I.eligible stage ∩ available).Nonempty)
    (hrank : badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available =
      (depth : ℕ∞))
    (hshorter : ∀ (childAvailable : Finset I.Tool) (childDepth : ℕ),
      errorRank (I.compatibility.drop (stage.val + 1)) childAvailable = (childDepth : ℕ∞) →
        0 < childDepth ∧ 0 < input.suffixCoefficient (stage.val + 1) childAvailable ∧
          Tendsto (fun price : ℝ => input.healthyPenaltyReal (stage.val + 1) childAvailable price /
            (input.suffixCoefficient (stage.val + 1) childAvailable * iteratedLog childDepth price))
            atTop (𝓝 1)) :
    ∃ B : ℝ, 0 < B ∧
      Tendsto (fun price : ℝ => input.badPenaltyReal stage available price / iteratedLog depth price)
        atTop (𝓝 B) := by
  obtain ⟨B, hB, _, _, hlimit⟩ :=
    input.badPenaltyReal_leading_minimum_of_shorter stage available depth hnonempty hrank hshorter
  exact ⟨B, hB, hlimit⟩

theorem StatisticalInput.badPenaltyReal_empty_leading {I : Instance}
    (input : StatisticalInput I) (stage : I.Stage) (available : Finset I.Tool)
    (hempty : I.eligible stage ∩ available = ∅) :
    badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) available = 0 ∧
      (∀ price : ℝ, input.badPenaltyReal stage available price = price) ∧
      Tendsto (fun price : ℝ => input.badPenaltyReal stage available price / iteratedLog 0 price)
        atTop (𝓝 1) := by
  classical
  have hnone : ¬ (I.eligible stage ∩ available).Nonempty := by simp [hempty]
  have heq (price : ℝ) : input.badPenaltyReal stage available price = price := by
    simp only [StatisticalInput.badPenaltyReal, hnone, ↓reduceDIte]
  refine ⟨(badChildRank_eq_zero_iff _ _ _).mpr hempty, heq, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with price hp
  rw [heq, iteratedLog, div_self hp]

end PaperProofs.Common
