module

public import Common.PSTR_ST_LocalFeeAssembly_040

/-! Local-equation full-bill finite-stage cost steps and the one-stage/empty bases
for the inherited fixed selector induction. Original charges and cutoff
quantifiers are retained; every shorter-child performance IH is explicit. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

def Certified.freshGood {available : Finset I.Tool} (selector : Certified I available) (first : ℕ) :
    Certified (I.freshSuffix first) available :=
  LocalFees.inheritedGood selector first

def Certified.freshBad {available : Finset I.Tool} (selector : Certified I available)
    (first : ℕ) (tool : I.Tool) : Certified (I.freshSuffix first) (available.erase tool) :=
  LocalFees.inheritedBad selector first tool

namespace CostInduction

theorem selector_exists_finiteBad {available : Finset I.Tool} (selector : Certified I available)
    (first : I.Stage) (depth : ℕ+)
    (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad depth)) :
    ∃ tool, selector.choose first ∅ = some tool := by
  cases hpick : selector.choose first ∅ with
  | some tool => exact ⟨tool, rfl⟩
  | none =>
    have hempty := (selector.spec.none first ∅).mp hpick
    have hsem := referenceAvailableRankCase_semantics I available first ∅ (.finiteBad depth) hkind
    simp only [Finset.sdiff_empty] at hempty hsem
    have hzero := (badChildRank_eq_zero_iff (I.eligible first)
      (I.compatibility.drop (first.val + 1)) available).mpr hempty
    rw [hsem.2] at hzero
    have hpositive : (0 : ℕ∞) < (depth.val : ℕ∞) := by exact_mod_cast depth.pos
    exact ((ne_of_gt hpositive) hzero).elim

theorem expectedBill_finiteBad_step_of_shorter_cost
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J)
      (available : Finset J.Tool) (selector : Certified J available),
      J.stageCount < I.stageCount → Asymptotics.CostAsymptotics child available selector)
    (available : Finset I.Tool) (selector : Certified I available) (first nextStage : I.Stage)
    (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (depth : ℕ+) (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad depth)) :
    ∃ (tool : I.Tool) (bound cutoff : ℝ),
      selector.choose first ∅ = some tool ∧
      tool ∈ I.eligible first ∩ available ∧ 0 ≤ bound ∧ 0 < cutoff ∧
      ∀ (budget : ℚ), 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        ∀ (C : Contract I) (_hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I),
        expectedBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
          (referenceEntryLocalObservationPrice input available budget first [] +
            (Asymptotics.suffixObservationCost input nextStage available (selector.freshGood nextStage.val) (budget / 2) + ENNReal.ofReal bound)) +
            (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  obtain ⟨tool, hpick⟩ := selector_exists_finiteBad selector first depth hkind
  have htool := selector.spec.some first ∅ tool hpick
  have hsem := referenceAvailableRankCase_semantics I available first ∅ (.finiteBad depth) hkind
  simp only [Finset.sdiff_empty] at htool hsem
  have hchild := htool.2.trans hsem.2
  obtain ⟨bound, cutoff, hbound, hcutoff, hbadCost⟩ :=
    Asymptotics.badBranchCostBound_of_shorter_cost input ih first available depth.val
      (by have := depth.pos; omega) tool hchild (selector.freshBad (first.val + 1) tool)
  refine ⟨tool, bound, cutoff, hpick, htool.1, hbound, hcutoff, ?_⟩
  intro budget hbudget hsmall hcut C hcurrent accounting
  have hrisk : 0 < budget / 2 := by linarith
  have hquarter : budget / 2 ≤ 1 / 4 := by linarith
  have hbR : (0 : ℝ) < (budget : ℝ) := by exact_mod_cast hbudget
  have hcutHalf : ((budget / 2 : ℚ) : ℝ) < cutoff := by push_cast; linarith
  have hbad := hbadCost (budget / 2) hrisk hquarter hcutHalf
  have hfull := hbad (currentRelaxedContract (I.freshSuffix (first.val + 1)))
    ⟨rfl, rfl⟩ (zeroNormalAccounting (I.freshSuffix (first.val + 1)))
  let childBudget := 2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val)
  let child := selector.freshBad (first.val + 1) tool
  have hprojection := LocalFees.givenSelector_fullBill_eq_rawChild input available selector
    (first.val + 1) tool child (by rfl) childBudget
  have hweightedOld : ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) *
      LocalFees.rawChildFullBill input available selector (first.val + 1) tool childBudget ≤
        ENNReal.ofReal bound :=
    Eq.mp (congrArg (fun cost : ℝ≥0∞ =>
      ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) * cost ≤ ENNReal.ofReal bound) hprojection) hfull
  have hindex : first.val + 1 = nextStage.val := by omega
  have hcostIndex := LocalFees.rawChildFullBill_index_eq input available selector
    (first.val + 1) nextStage.val hindex tool childBudget
  have hweightedNext : ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) *
      LocalFees.rawChildFullBill input available selector nextStage.val tool childBudget ≤
        ENNReal.ofReal bound :=
    Eq.mp (congrArg (fun cost : ℝ≥0∞ =>
      ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) * cost ≤ ENNReal.ofReal bound) hcostIndex) hweightedOld
  exact LocalFees.finiteBad_full_bill_of_weighted_rawChild input C hcurrent.1 accounting available selector
    budget hbudget hsmall first nextStage hfirst hnext depth hkind tool hpick
    (selector.freshGood nextStage.val) (by rfl) bound hweightedNext


theorem expectedObservationBill_single_stage_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (hsize : I.stageCount = 1)
    (first : I.Stage) (hfirst : first.val = 0) :
    expectedObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
      referenceEntryLocalObservationPrice input available budget first [] := by
  classical
  have hlegal := rule_uncapped_legal selector.choose input C hearly accounting available budget none
  rw [expectedObservationBill_eq_sum_stage input C .uncapped accounting _ hlegal
    (policy selector.choose input C hearly accounting available budget none).measurable_rule]
  have heq (other : I.Stage) : other = first := by
    apply Fin.ext
    have ho : other.val < I.stageCount := other.isLt
    omega
  rw [Finset.sum_eq_single first (fun other _ hne => (hne (heq other)).elim) (by simp)]
  exact Fees.selectorInitialStageObservationBill_le_localPrice input C hearly accounting available selector budget hbudget hsmall first hfirst

theorem expectedObservationBill_empty
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hsize : I.stageCount = 0) :
    expectedObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) = 0 := by
  have : IsEmpty I.Stage := ⟨fun stage => by have hs : stage.val < I.stageCount := stage.isLt; omega⟩
  rw [expectedObservationBill_eq_sum_stage input C .uncapped accounting _
    (rule_uncapped_legal selector.choose input C hearly accounting available budget none)
    (policy selector.choose input C hearly accounting available budget none).measurable_rule]
  simp


theorem costAsymptotics_single_stage (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available)
    (hsize : I.stageCount = 1) : Asymptotics.CostAsymptotics input available selector := by
  intro depth hrank epsilon hepsilon
  let first : I.Stage := ⟨0, by change 0 < I.stageCount; omega⟩
  have hfirst : first.val = 0 := rfl
  have hfinite : errorRank I.compatibility available ≠ ⊤ := by
    rw [hrank]
    exact ENat.natCast_ne_top depth
  have hrankOne := (reference_single_stage_finite_rank first hfirst hsize available hfinite).2
  have hd : depth = 1 := ENat.natCast_inj.mp (hrank.symm.trans hrankOne)
  subst depth
  let E := input.experiment first
  let offset := Real.log (referenceQuotaConstant I.stageCount : ℝ) + E.logIncrementBound true +
    2 * |Real.log (E.priorReal true / E.priorReal false)|
  let fee : ℝ≥0∞ := (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection
  have hfee : fee ≠ ⊤ := ENNReal.mul_ne_top (by finiteness) input.fees.maxCorrection_lt_top.ne
  obtain ⟨cutoff, hcutoff, hscalar⟩ := LocalFees.log_affine_cutoff_local E.coefficient E.coefficient_pos offset fee.toReal
    ENNReal.toReal_nonneg epsilon hepsilon
  refine ⟨cutoff, hcutoff, ?_⟩
  intro budget hbudget hsmall hcut C hcurrent accounting
  have hb : (0 : ℝ) < (budget : ℝ) := by exact_mod_cast hbudget
  have hs := hscalar (budget : ℝ) hb hcut
  have hobs := expectedObservationBill_single_stage_le input C hcurrent.1 accounting available selector
    budget hbudget hsmall hsize first hfirst
  have hprice := referenceEntryLocalObservationPrice_le_global input available budget hbudget hsmall first []
  have hbound := (LocalFees.raw_expectedBill_le_observation_add selector.choose input C hcurrent.1 accounting
    available budget none (Measure.dirac ())).trans
      (add_le_add (hobs.trans hprice) le_rfl)
  change expectedBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
    ENNReal.ofReal (E.coefficient * (Real.log ((referenceQuotaConstant I.stageCount : ℝ) / (budget : ℝ)) +
      E.logIncrementBound true + 2 * |Real.log (E.priorReal true / E.priorReal false)|)) + fee at hbound
  have hC : (0 : ℝ) < (referenceQuotaConstant I.stageCount : ℝ) := by
    unfold referenceQuotaConstant
    positivity
  have hoffset : Real.log ((referenceQuotaConstant I.stageCount : ℝ) / (budget : ℝ)) +
      E.logIncrementBound true + 2 * |Real.log (E.priorReal true / E.priorReal false)| =
        Real.log (budget : ℝ)⁻¹ + offset := by
    rw [Real.log_div hC.ne' hb.ne', Real.log_inv]
    dsimp [offset]
    ring
  rw [hoffset] at hbound
  have hcoefficient := reference_single_stage_coefficient input first hfirst hsize available hfinite
  calc
    _ ≤ ENNReal.ofReal (E.coefficient * (Real.log (budget : ℝ)⁻¹ + offset)) + fee := hbound
    _ = ENNReal.ofReal (E.coefficient * (Real.log (budget : ℝ)⁻¹ + offset) + fee.toReal) := by
      rw [ENNReal.ofReal_add hs.1 ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfee]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by simpa only [hcoefficient, iteratedLog] using hs.2)

theorem costAsymptotics_empty (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available)
    (hsize : I.stageCount = 0) : Asymptotics.CostAsymptotics input available selector := by
  intro depth hrank
  have hnil : I.compatibility = [] := List.length_eq_zero_iff.mp hsize
  rw [hnil, errorRank_terminal] at hrank
  exact (ENat.top_ne_natCast depth hrank).elim


theorem expectedBill_noTool_step (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (first nextStage : I.Stage)
    (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (hkind : referenceAvailableRankCase I available first ∅ = some .noTool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I) :
    expectedBill input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
      (referenceEntryLocalObservationPrice input available budget first [] +
        Asymptotics.suffixObservationCost input nextStage available (selector.freshGood nextStage.val) (budget / 2)) +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  exact LocalFees.noTool_full_bill_givenSelector input C hcurrent.1 accounting available selector budget
    hbudget hsmall first nextStage hfirst hnext hkind (selector.freshGood nextStage.val) (by rfl)

end CostInduction

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector
