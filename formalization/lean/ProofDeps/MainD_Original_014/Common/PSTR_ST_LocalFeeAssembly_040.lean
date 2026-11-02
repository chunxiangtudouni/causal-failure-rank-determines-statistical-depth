module

public import Common.PSTR_ST_LocalFeeEqualities_039

/-! Local complete-fee assembly and scalar cutoff; the original charges,
weighted child fee and failure/infinite-bill scope are unchanged. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.LocalFees

open PaperProofs.Statistics

variable {I : Instance}

/-- Local replacement interface for 034's final noTool assembly. All
original full-prefix charges remain. The child premise is only its chooser
projection, supplied by rfl for the inherited good certificate. -/
theorem noTool_full_bill_givenSelector (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (hkind : referenceAvailableRankCase I available first ∅ = some .noTool)
    (child : Certified (I.freshSuffix nextStage.val) available)
    (hchoose : child.choose = MaxSelector.restrict I selector.choose nextStage.val ∅) :
    expectedBill input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
      (referenceEntryLocalObservationPrice input available budget first [] +
        Asymptotics.suffixObservationCost input nextStage available child (budget / 2)) +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  have hgood := goodObservationCost_eq_givenSelector input available selector nextStage child hchoose (budget / 2)
  have hobs := BranchCost.expectedObservationBill_noTool_le input C hearly accounting available selector
    budget hbudget hsmall first nextStage hfirst hnext hkind
  have hpriceEq := congrArg (fun good : ℝ≥0∞ =>
    referenceEntryLocalObservationPrice input available budget first [] + good) hgood
  have hobs' := hobs.trans hpriceEq.le
  have hbill := raw_expectedBill_le_observation_add selector.choose input C hearly accounting available
    budget none (Measure.dirac ())
  exact hbill.trans (add_le_add hobs' le_rfl)

/-- Local replacement interface for 034's finiteBad final assembly. The
weighted raw child full-bill bound is exactly the already derived IH result;
it is kept separate from chooser projection and numerical ENNReal assembly. -/
theorem finiteBad_full_bill_of_weighted_rawChild (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (depth : ℕ+) (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad depth))
    (tool : I.Tool) (hpick : selector.choose first ∅ = some tool)
    (goodChild : Certified (I.freshSuffix nextStage.val) available)
    (hgood : goodChild.choose = MaxSelector.restrict I selector.choose nextStage.val ∅)
    (bound : ℝ)
    (hweighted : ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) *
      expectedBill (input.freshSuffix nextStage.val)
        (currentRelaxedContract (I.freshSuffix nextStage.val)) .uncapped
        (zeroNormalAccounting (I.freshSuffix nextStage.val))
        (MaxSelector.rule (MaxSelector.restrict I selector.choose nextStage.val {tool})
          (input.freshSuffix nextStage.val) (available.erase tool)
          (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val)) none)
        (Measure.dirac ()) ≤ ENNReal.ofReal bound) :
    expectedBill input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
      (referenceEntryLocalObservationPrice input available budget first [] +
        (Asymptotics.suffixObservationCost input nextStage available goodChild (budget / 2) + ENNReal.ofReal bound)) +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  let childBudget := 2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val)
  have hbadObs : BranchCost.badObservationCost input available selector nextStage tool childBudget ≤
      expectedBill (input.freshSuffix nextStage.val)
        (currentRelaxedContract (I.freshSuffix nextStage.val)) .uncapped
        (zeroNormalAccounting (I.freshSuffix nextStage.val))
        (MaxSelector.rule (MaxSelector.restrict I selector.choose nextStage.val {tool})
          (input.freshSuffix nextStage.val) (available.erase tool) childBudget none) (Measure.dirac ()) :=
    expectedObservationBill_le_actual (input.freshSuffix nextStage.val)
      (currentRelaxedContract (I.freshSuffix nextStage.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix nextStage.val))
      (MaxSelector.rule (MaxSelector.restrict I selector.choose nextStage.val {tool})
        (input.freshSuffix nextStage.val) (available.erase tool) childBudget none) (Measure.dirac ())
  have hweightedObs := (mul_le_mul' (le_refl (ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ))) hbadObs).trans hweighted
  have hobs := BranchCost.expectedObservationBill_finiteBad_le input C hearly accounting available selector
    budget hbudget hsmall first nextStage hfirst hnext depth hkind tool hpick
  have hobsBound := hobs.trans (add_le_add le_rfl (add_le_add le_rfl hweightedObs))
  have hgoodEq := goodObservationCost_eq_givenSelector input available selector nextStage goodChild hgood (budget / 2)
  have hpriceEq := congrArg (fun good : ℝ≥0∞ =>
    referenceEntryLocalObservationPrice input available budget first [] + (good + ENNReal.ofReal bound)) hgoodEq
  have hobs' := hobsBound.trans hpriceEq.le
  have hbill := raw_expectedBill_le_observation_add selector.choose input C hearly accounting available budget none (Measure.dirac ())
  exact hbill.trans (add_le_add hobs' le_rfl)

/-- Same scalar goal as 034:135–158, with every arithmetic inference local.
In particular no nlinarith call receives the full exp/log/division context. -/
theorem log_affine_cutoff_local (A : ℝ) (hA : 0 < A) (offset fee : ℝ)
    (hfee : 0 ≤ fee) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ risk : ℝ, 0 < risk → risk < cutoff →
      0 ≤ A * (Real.log risk⁻¹ + offset) ∧
        A * (Real.log risk⁻¹ + offset) + fee ≤ (1 + epsilon) * A * Real.log risk⁻¹ := by
  let extra := (fee + A * |offset|) / (epsilon * A)
  let M := |offset| + extra + 1
  have hden : 0 < epsilon * A := mul_pos hepsilon hA
  have hextra : 0 ≤ extra :=
    div_nonneg (add_nonneg hfee (mul_nonneg hA.le (abs_nonneg offset))) hden.le
  have hMabs : |offset| ≤ M := by
    exact (le_add_of_nonneg_right hextra).trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  have hMextra : extra ≤ M := by
    exact (le_add_of_nonneg_left (abs_nonneg offset)).trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  refine ⟨Real.exp (-M), Real.exp_pos _, ?_⟩
  intro risk hrisk hsmall
  let L := Real.log risk⁻¹
  have hl : M < L := by
    have hlog := Real.log_lt_log hrisk hsmall
    rw [Real.log_exp] at hlog
    dsimp only [L]
    rw [Real.log_inv]
    linarith only [hlog]
  have habs : |offset| ≤ L := hMabs.trans hl.le
  have hthreshold : extra ≤ L := hMextra.trans hl.le
  have hpay : fee + A * |offset| ≤ L * (epsilon * A) := (div_le_iff₀ hden).mp hthreshold
  have hterm : A * offset ≤ A * |offset| := mul_le_mul_of_nonneg_left (le_abs_self offset) hA.le
  have hpositive : 0 ≤ L + offset := by
    calc
      0 = |offset| + -|offset| := by ring
      _ ≤ L + offset := add_le_add habs (neg_abs_le offset)
  refine ⟨mul_nonneg hA.le hpositive, ?_⟩
  calc
    A * (L + offset) + fee = A * L + (fee + A * offset) := by ring
    _ ≤ A * L + (fee + A * |offset|) :=
      add_le_add (le_refl (A * L)) (add_le_add (le_refl fee) hterm)
    _ ≤ A * L + (L * (epsilon * A)) := add_le_add (le_refl (A * L)) hpay
    _ = (1 + epsilon) * A * L := by ring

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.LocalFees
