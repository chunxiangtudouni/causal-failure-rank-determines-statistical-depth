module

public import PaperProofs.Common.PSTR_ST_SelectorCostInduction_041

/-! Complete actual finite-rank variable-fee strong induction for every
fixed legal maximizing selector. The ambient selector is fixed before risk,
contract and accounting; both shorter children inherit it. No unresolved
parent/child price, recurrence or performance hypothesis survives. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Asymptotics

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

theorem costAsymptotics_of_shorter_cost
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J)
      (available : Finset J.Tool) (selector : Certified J available),
      J.stageCount < I.stageCount → CostAsymptotics child available selector)
    (available : Finset I.Tool) (selector : Certified I available) :
    CostAsymptotics input available selector := by
  by_cases hsmallSize : I.stageCount ≤ 1
  · by_cases hzero : I.stageCount = 0
    · exact CostInduction.costAsymptotics_empty input available selector hzero
    · have hone : I.stageCount = 1 := by omega
      exact CostInduction.costAsymptotics_single_stage input available selector hone
  intro depth hrank
  let first : I.Stage := ⟨0, by change 0 < I.stageCount; omega⟩
  let nextStage : I.Stage := ⟨1, by change 1 < I.stageCount; omega⟩
  have hfirst : first.val = 0 := rfl
  have hnext : nextStage.val = 1 := rfl
  have hfinite : errorRank I.compatibility available ≠ ⊤ := by rw [hrank]; exact ENat.natCast_ne_top depth
  have hdepth : 1 ≤ depth := by
    have hp := errorRank_pos I.compatibility available
    rw [hrank] at hp
    have : 0 < depth := by exact_mod_cast hp
    omega
  have hrec := I.errorRank_head_freshSuffix first hfirst available
  have hgoodOrder : (depth : ℕ∞) ≤ errorRank (I.freshSuffix nextStage.val).compatibility available := by
    rw [← hrank, hrec]
    exact min_le_left _ _
  have hbadOrder : (depth : ℕ∞) ≤
      1 + badChildRank (I.eligible first) (I.freshSuffix 1).compatibility available := by
    rw [← hrank, hrec]
    exact min_le_right _ _
  obtain ⟨kind, hkind⟩ := referenceAvailableRankCase_exists I available first ∅
  cases kind with
  | infiniteRank =>
    have hsem := referenceAvailableRankCase_semantics I available first ∅ .infiniteRank hkind
    have htop : errorRank I.compatibility available = ⊤ := by
      simpa only [hfirst, List.drop_zero, Finset.sdiff_empty] using hsem
    exact (hfinite htop).elim
  | noTool =>
    have hsem := referenceAvailableRankCase_semantics I available first ∅ .noTool hkind
    simp only [Finset.sdiff_empty] at hsem
    have hbad : badChildRank (I.eligible first) (I.freshSuffix 1).compatibility available = 0 :=
      (badChildRank_eq_zero_iff _ _ _).mpr hsem.2
    rw [hbad, add_zero] at hbadOrder
    have hdUpper : depth ≤ 1 := by exact_mod_cast hbadOrder
    have hdOne : depth = 1 := by omega
    subst depth
    have hcoefficient : input.orderedCoefficient available =
        (if errorRank (I.freshSuffix nextStage.val).compatibility available = (1 : ℕ∞) then
          (input.freshSuffix nextStage.val).orderedCoefficient available else 0) +
          (input.experiment first).coefficient := by
      simpa only [hnext, hrank, hbad, zero_add, ENat.natCast_one, ite_true] using
        input.orderedCoefficient_head_freshSuffix first hfirst available hfinite
    apply costAsymptotics_initial_step_of_bounds input ih available selector first nextStage (selector.freshGood nextStage.val)
      (by simp only [hnext]; norm_num) 1 (by norm_num) hrank hgoodOrder
      (input.experiment first).coefficient (input.experiment first).coefficient_pos.le hcoefficient
      0 1 (by norm_num) (by norm_num)
      (referenceEntryLocalObservationPrice_noTool_asymptotic input available first)
    intro budget hbudget hsmall _ C hcurrent accounting
    simpa only [ENNReal.ofReal_zero, add_zero] using
      CostInduction.expectedBill_noTool_step input available selector first nextStage hfirst hnext hkind
        budget hbudget hsmall C hcurrent accounting
  | finiteBad badDepth =>
    have hsem := referenceAvailableRankCase_semantics I available first ∅ (.finiteBad badDepth) hkind
    simp only [Finset.sdiff_empty] at hsem
    have hbad : badChildRank (I.eligible first) (I.freshSuffix 1).compatibility available =
        (badDepth.val : ℕ∞) := by
      simpa only [Instance.freshSuffix, hfirst, Nat.zero_add] using hsem.2
    have horderBad : depth ≤ badDepth.val + 1 := by
      rw [hbad] at hbadOrder
      exact ENat.natCast_le_natCast.mp (by
        simpa only [ENat.natCast_add, ENat.natCast_one, add_comm] using hbadOrder)
    let localLead := (input.experiment first).coefficient * (if depth = badDepth.val + 1 then 1 else 0)
    have hlocalLead : 0 ≤ localLead := by
      dsimp [localLead]
      have hA := (input.experiment first).coefficient_pos
      split_ifs <;> positivity
    have hcrit : ((badDepth.val : ℕ∞) + 1 = (depth : ℕ∞)) ↔ depth = badDepth.val + 1 := by
      rw [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_inj]
      omega
    have hcoefficient : input.orderedCoefficient available =
        (if errorRank (I.freshSuffix nextStage.val).compatibility available = (depth : ℕ∞) then
          (input.freshSuffix nextStage.val).orderedCoefficient available else 0) + localLead := by
      simpa only [hnext, hrank, hbad, hcrit, localLead, mul_ite, mul_one, mul_zero] using
        input.orderedCoefficient_head_freshSuffix first hfirst available hfinite
    obtain ⟨_, bound, stepCutoff, _, _, hbound, hstepCutoff, hstep⟩ :=
      CostInduction.expectedBill_finiteBad_step_of_shorter_cost input ih available selector first nextStage hfirst hnext badDepth hkind
    exact costAsymptotics_initial_step_of_bounds input ih available selector first nextStage (selector.freshGood nextStage.val)
      (by simp only [hnext]; norm_num) depth hdepth hrank hgoodOrder localLead hlocalLead hcoefficient
      bound stepCutoff hbound hstepCutoff
      (referenceEntryLocalObservationPrice_finiteBad_asymptotic input available first hfirst badDepth hkind depth hdepth horderBad)
      hstep


theorem costAsymptotics (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) : CostAsymptotics input available selector := by
  have hall : ∀ n : ℕ, ∀ (J : Instance) (child : StatisticalInput J)
      (tools : Finset J.Tool) (choose : Certified J tools), J.stageCount = n →
        CostAsymptotics child tools choose := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J child tools choose hsize
      apply costAsymptotics_of_shorter_cost child ?_ tools choose
      intro K grandchild remaining inherited hshort
      exact ih K.stageCount (by omega) K grandchild remaining inherited rfl
  exact hall I.stageCount I input available selector rfl

/-- Original TABLE ideal expected bill, with every selector/spec/IH/recurrence
obligation discharged. This is the finite-rank fee input to original SharpUpper,
and is not a generic-picker run substitution. -/
theorem tableIdealCostAsymptotics (input : StatisticalInput I)
    (hlaminar : PaperProofs.Structure.LaminarTree.LaminarSchedule I.compatibility)
    (available : Finset I.Tool) (depth : ℕ)
    (hrank : errorRank I.compatibility available = (depth : ℕ∞))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        ∀ (C : Contract I) (_hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I),
          expectedBill input C .uncapped accounting
            (CompactPrice.tableRule input available budget none) (Measure.dirac ()) ≤
              ENNReal.ofReal ((1 + epsilon) * input.orderedCoefficient available *
                iteratedLog depth (budget : ℝ)⁻¹) := by
  have hcost := costAsymptotics input available (Certified.table I hlaminar available)
    depth hrank epsilon hepsilon
  simpa only [Certified.table_rule] using hcost

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Asymptotics
