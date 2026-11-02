module

public import Common.PSTR_ST_SelectorInfinite_023

/-! Numerical and strictly-shorter-input cost steps with the inherited fixed
selector explicit. This module supplies no unproved actual branch recurrence;
that separate execution obligation remains a conclusion of the full proof. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Asymptotics

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

/-- Uniform in the original contracts/accounting. The selector is fixed
before epsilon/cutoff/budget, with no runtime or performance field. -/
def CostAsymptotics (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) : Prop :=
  ∀ depth : ℕ, errorRank I.compatibility available = (depth : ℕ∞) →
    ∀ epsilon : ℝ, 0 < epsilon → ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        ∀ (C : Contract I) (_hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I),
          expectedBill input C .uncapped accounting
            (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
              ENNReal.ofReal ((1 + epsilon) * input.orderedCoefficient available *
                iteratedLog depth (budget : ℝ)⁻¹)

noncomputable def suffixObservationCost (input : StatisticalInput I) (stage : I.Stage)
    (available : Finset I.Tool) (childSelector : Certified (I.freshSuffix stage.val) available)
    (budget : ℚ) : ℝ≥0∞ :=
  expectedObservationBill (input.freshSuffix stage.val)
    (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
    (zeroNormalAccounting (I.freshSuffix stage.val))
    (MaxSelector.rule childSelector.choose (input.freshSuffix stage.val) available budget none) (Measure.dirac ())

theorem suffixObservationCost_finite_of_shorter_cost
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J)
      (available : Finset J.Tool) (selector : Certified J available),
      J.stageCount < I.stageCount → CostAsymptotics child available selector)
    (stage : I.Stage) (hstage : 0 < stage.val) (available : Finset I.Tool) (childSelector : Certified (I.freshSuffix stage.val) available) (depth : ℕ)
    (hrank : errorRank (I.freshSuffix stage.val).compatibility available = (depth : ℕ∞))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ (budget : ℚ), 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        suffixObservationCost input stage available childSelector (budget / 2) ≤
          ENNReal.ofReal ((1 + epsilon) * (input.freshSuffix stage.val).orderedCoefficient available *
            iteratedLog depth (1 / ((budget / 2 : ℚ) : ℝ))) := by
  have hshort : (I.freshSuffix stage.val).stageCount < I.stageCount := by
    rw [I.freshSuffix_stageCount]
    have hs : stage.val < I.stageCount := stage.isLt
    omega
  obtain ⟨cutoff, hcutoff, hcost⟩ :=
    ih (I.freshSuffix stage.val) (input.freshSuffix stage.val) available childSelector hshort depth hrank epsilon hepsilon
  refine ⟨cutoff, hcutoff, ?_⟩
  intro budget hbudget hsmall hcut
  have hhalf : 0 < budget / 2 := by linarith
  have hhalfSmall : budget / 2 ≤ 1 / 2 := by linarith
  have hbR : (0 : ℝ) < (budget : ℝ) := by exact_mod_cast hbudget
  have hhalfCut : ((budget / 2 : ℚ) : ℝ) < cutoff := by push_cast; linarith
  have hactual := hcost (budget / 2) hhalf hhalfSmall hhalfCut
    (currentRelaxedContract (I.freshSuffix stage.val)) ⟨rfl, rfl⟩
    (zeroNormalAccounting (I.freshSuffix stage.val))
  change expectedBill (input.freshSuffix stage.val) (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
    (zeroNormalAccounting (I.freshSuffix stage.val))
    (MaxSelector.rule childSelector.choose (input.freshSuffix stage.val) available (budget / 2) none) (Measure.dirac ()) ≤ _ at hactual
  exact (expectedObservationBill_le_actual (input.freshSuffix stage.val)
    (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
    (zeroNormalAccounting (I.freshSuffix stage.val))
    (MaxSelector.rule childSelector.choose (input.freshSuffix stage.val) available (budget / 2) none) (Measure.dirac ())).trans
      (by simpa only [one_div] using hactual)

theorem suffixObservationCost_asymptotic_of_shorter_cost
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J)
      (available : Finset J.Tool) (selector : Certified J available),
      J.stageCount < I.stageCount → CostAsymptotics child available selector)
    (stage : I.Stage) (hstage : 0 < stage.val) (available : Finset I.Tool) (childSelector : Certified (I.freshSuffix stage.val) available)
    (goodDepth depth : ℕ) (hdepth : 1 ≤ depth) (horder : depth ≤ goodDepth)
    (hrank : errorRank (I.freshSuffix stage.val).compatibility available = (goodDepth : ℕ∞))
    (eta : ℝ) (heta : 0 < eta) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 →
      (budget : ℝ) < cutoff →
      suffixObservationCost input stage available childSelector (budget / 2) ≤
        ENNReal.ofReal (((if goodDepth = depth then
          (input.freshSuffix stage.val).orderedCoefficient available else 0) + eta) *
          iteratedLog depth (1 / (budget : ℝ))) := by
  let coefficient := (input.freshSuffix stage.val).orderedCoefficient available
  have hcoefficient : 0 < coefficient :=
    (input.freshSuffix stage.val).orderedCoefficient_pos available (by rw [hrank]; exact ENat.natCast_ne_top goodDepth)
  let childEpsilon := eta / (2 * coefficient)
  have hchildEpsilon : 0 < childEpsilon := by dsimp [childEpsilon]; positivity
  obtain ⟨childCutoff, hchildCutoff, hchild⟩ := suffixObservationCost_finite_of_shorter_cost
    input ih stage hstage available childSelector goodDepth hrank childEpsilon hchildEpsilon
  have hratio : Tendsto (fun risk : ℚ => iteratedLog goodDepth (1 / ((risk / 2 : ℚ) : ℝ)) /
      iteratedLog depth (1 / (risk : ℝ))) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (if goodDepth = depth then 1 else 0)) := by
    by_cases heq : goodDepth = depth
    · subst goodDepth
      simpa only [ite_true] using rationalRisk_iteratedLog_half_div_tendsto_one depth hdepth
    · simpa only [heq, ite_false] using rationalRisk_iteratedLog_half_div_tendsto_zero depth goodDepth (by omega)
  let allowance := fun risk : ℚ => (1 + childEpsilon) * coefficient *
    iteratedLog goodDepth (1 / ((risk / 2 : ℚ) : ℝ))
  have hlimit : Tendsto (fun risk : ℚ => allowance risk / iteratedLog depth (1 / (risk : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((1 + childEpsilon) * coefficient * (if goodDepth = depth then 1 else 0))) := by
    simpa only [allowance, mul_div_assoc] using hratio.const_mul ((1 + childEpsilon) * coefficient)
  have hlt : (1 + childEpsilon) * coefficient * (if goodDepth = depth then 1 else 0) <
      (if goodDepth = depth then coefficient else 0) + eta := by
    by_cases heq : goodDepth = depth
    · simp only [heq, ite_true, mul_one]
      have he : (1 + childEpsilon) * coefficient = coefficient + eta / 2 := by
        dsimp [childEpsilon]
        field_simp
      rw [he]
      linarith
    · simpa only [heq, ite_false, mul_zero, zero_add] using heta
  obtain ⟨numericCutoff, hnumericCutoff, hnumeric⟩ := rationalRisk_cutoff_of_ratio_limit depth allowance _ _ hlt hlimit
  refine ⟨min childCutoff numericCutoff, lt_min hchildCutoff hnumericCutoff, ?_⟩
  intro budget hbudget hsmall hcut
  exact (hchild budget hbudget hsmall (hcut.trans_le (min_le_left _ _))).trans
    (ENNReal.ofReal_le_ofReal (hnumeric budget hbudget (hcut.trans_le (min_le_right _ _))))

theorem suffixObservationCost_head_asymptotic
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J)
      (available : Finset J.Tool) (selector : Certified J available),
      J.stageCount < I.stageCount → CostAsymptotics child available selector)
    (stage : I.Stage) (hstage : 0 < stage.val) (available : Finset I.Tool) (childSelector : Certified (I.freshSuffix stage.val) available)
    (depth : ℕ) (hdepth : 1 ≤ depth)
    (horder : (depth : ℕ∞) ≤ errorRank (I.freshSuffix stage.val).compatibility available)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 →
      (budget : ℝ) < cutoff →
      suffixObservationCost input stage available childSelector (budget / 2) ≤
        ENNReal.ofReal (((if errorRank (I.freshSuffix stage.val).compatibility available = (depth : ℕ∞) then
          (input.freshSuffix stage.val).orderedCoefficient available else 0) + eta) *
          iteratedLog depth (1 / (budget : ℝ))) := by
  by_cases htop : errorRank (I.freshSuffix stage.val).compatibility available = ⊤
  · refine ⟨1, by norm_num, ?_⟩
    intro budget hbudget hsmall _
    have hhalf : 0 < budget / 2 := by linarith
    have hhalfSmall : budget / 2 ≤ 1 / 2 := by linarith
    unfold suffixObservationCost
    rw [Infinite.selectorExpectedObservationBill_infiniteRank (input.freshSuffix stage.val)
      (currentRelaxedContract (I.freshSuffix stage.val)) rfl (zeroNormalAccounting (I.freshSuffix stage.val))
      available childSelector (budget / 2) hhalf hhalfSmall htop none (Measure.dirac ())]
    exact bot_le
  · obtain ⟨goodDepth, hgood⟩ := ENat.ne_top_iff_exists.mp htop
    have horderNat : depth ≤ goodDepth := by
      exact ENat.natCast_le_natCast.mp (hgood ▸ horder)
    have hbound := suffixObservationCost_asymptotic_of_shorter_cost input ih stage hstage
      available childSelector goodDepth depth hdepth horderNat hgood.symm eta heta
    simpa only [← hgood, ENat.natCast_inj] using hbound


theorem costAsymptotics_initial_step_of_bounds
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J)
      (available : Finset J.Tool) (selector : Certified J available),
      J.stageCount < I.stageCount → CostAsymptotics child available selector)
    (available : Finset I.Tool) (selector : Certified I available) (first nextStage : I.Stage)
    (childSelector : Certified (I.freshSuffix nextStage.val) available) (hnext : 0 < nextStage.val)
    (depth : ℕ) (hdepth : 1 ≤ depth)
    (hrank : errorRank I.compatibility available = (depth : ℕ∞))
    (hgoodOrder : (depth : ℕ∞) ≤ errorRank (I.freshSuffix nextStage.val).compatibility available)
    (localLead : ℝ) (hlocalLead : 0 ≤ localLead)
    (hcoefficient : input.orderedCoefficient available =
      (if errorRank (I.freshSuffix nextStage.val).compatibility available = (depth : ℕ∞) then
        (input.freshSuffix nextStage.val).orderedCoefficient available else 0) + localLead)
    (bound stepCutoff : ℝ) (hbound : 0 ≤ bound) (hstepCutoff : 0 < stepCutoff)
    (hlocal : ∀ eta : ℝ, 0 < eta → ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        referenceEntryLocalObservationPrice input available budget first [] ≤
          ENNReal.ofReal ((localLead + eta) * iteratedLog depth (1 / (budget : ℝ))))
    (hstep : ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < stepCutoff →
      ∀ (C : Contract I) (_hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I),
        expectedBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
          (referenceEntryLocalObservationPrice input available budget first [] +
            (suffixObservationCost input nextStage available childSelector (budget / 2) + ENNReal.ofReal bound)) +
            (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        ∀ (C : Contract I) (_hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I),
          expectedBill input C .uncapped accounting
            (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
            ENNReal.ofReal ((1 + epsilon) * input.orderedCoefficient available *
              iteratedLog depth (budget : ℝ)⁻¹) := by
  intro epsilon hepsilon
  have hfinite : errorRank I.compatibility available ≠ ⊤ := by rw [hrank]; exact ENat.natCast_ne_top depth
  have hcoefficientPositive := input.orderedCoefficient_pos available hfinite
  let goodLead := if errorRank (I.freshSuffix nextStage.val).compatibility available = (depth : ℕ∞) then
    (input.freshSuffix nextStage.val).orderedCoefficient available else 0
  have hgoodLead : 0 ≤ goodLead := by
    dsimp [goodLead]
    split_ifs with heq
    · exact ((input.freshSuffix nextStage.val).orderedCoefficient_pos available
        (by rw [heq]; exact ENat.natCast_ne_top depth)).le
    · exact le_rfl
  change input.orderedCoefficient available = goodLead + localLead at hcoefficient
  let eta := epsilon * input.orderedCoefficient available / 4
  have heta : 0 < eta := by dsimp [eta]; positivity
  let corrections : ℝ≥0∞ := (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection
  have hcorrections : corrections ≠ ⊤ :=
    ENNReal.mul_ne_top (by finiteness) input.fees.maxCorrection_lt_top.ne
  obtain ⟨localCutoff, hlocalCutoff, hhead⟩ := hlocal eta heta
  obtain ⟨goodCutoff, hgoodCutoff, hgood⟩ := suffixObservationCost_head_asymptotic
    input ih nextStage hnext available childSelector depth hdepth hgoodOrder eta heta
  obtain ⟨constantCutoff, hconstantCutoff, hconstant⟩ :=
    rationalRisk_constant_cutoff depth (bound + corrections.toReal) eta heta
  refine ⟨min stepCutoff (min localCutoff (min goodCutoff constantCutoff)),
    lt_min hstepCutoff (lt_min hlocalCutoff (lt_min hgoodCutoff hconstantCutoff)), ?_⟩
  intro budget hbudget hsmall hcut C hcurrent accounting
  obtain ⟨hstepCut, hrest⟩ := lt_min_iff.mp hcut
  obtain ⟨hlocalCut, hrest⟩ := lt_min_iff.mp hrest
  obtain ⟨hgoodCut, hconstantCut⟩ := lt_min_iff.mp hrest
  have hheadBound := hhead budget hbudget hsmall hlocalCut
  have hgoodBound := hgood budget hbudget hsmall hgoodCut
  have hconstantBound := hconstant budget hbudget hconstantCut
  have hparts := ennreal_parent_three_allowances
    (referenceEntryLocalObservationPrice input available budget first [])
    (suffixObservationCost input nextStage available childSelector (budget / 2)) corrections
    bound localLead goodLead eta (iteratedLog depth (1 / (budget : ℝ)))
    hcorrections hbound hlocalLead hgoodLead heta hheadBound hgoodBound hconstantBound
  have hscale : 0 ≤ iteratedLog depth (1 / (budget : ℝ)) := by
    have hc : 0 ≤ corrections.toReal := ENNReal.toReal_nonneg
    nlinarith
  have hcoefficientAllowance : localLead + goodLead + 3 * eta ≤
      (1 + epsilon) * input.orderedCoefficient available := by
    dsimp [eta]
    have hpositive := mul_pos hepsilon hcoefficientPositive
    nlinarith [hcoefficient]
  calc
    _ ≤ (referenceEntryLocalObservationPrice input available budget first [] +
          (suffixObservationCost input nextStage available childSelector (budget / 2) + ENNReal.ofReal bound)) +
          corrections := hstep budget hbudget hsmall hstepCut C hcurrent accounting
    _ ≤ ENNReal.ofReal ((localLead + goodLead + 3 * eta) *
        iteratedLog depth (1 / (budget : ℝ))) := hparts
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      simpa only [one_div] using mul_le_mul_of_nonneg_right hcoefficientAllowance hscale)


/-- The fixed inherited bad child is multiplied by the ORIGINAL local target.
The O(1) allowance follows solely from the strictly shorter cost induction,
uniform in every original current-allocation contract and accounting. -/
theorem badBranchCostBound_of_shorter_cost (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J)
      (available : Finset J.Tool) (selector : Certified J available),
      J.stageCount < I.stageCount → CostAsymptotics child available selector)
    (stage : I.Stage) (available : Finset I.Tool) (depth : ℕ) (hdepth : 1 ≤ depth)
    (tool : I.Tool)
    (hchildRank : errorRank (I.compatibility.drop (stage.val + 1)) (available.erase tool) = (depth : ℕ∞))
    (childSelector : Certified (I.freshSuffix (stage.val + 1)) (available.erase tool)) :
    ∃ (bound cutoff : ℝ), 0 ≤ bound ∧ 0 < cutoff ∧
      ∀ risk : ℚ, 0 < risk → risk ≤ 1 / 4 → (risk : ℝ) < cutoff →
        ∀ (C : Contract (I.freshSuffix (stage.val + 1))) (_hcurrent : C.IsCurrentAllocation)
          (accounting : NormalAccounting (I.freshSuffix (stage.val + 1))),
          ENNReal.ofReal (controllerTarget risk depth : ℝ) *
            expectedBill (input.freshSuffix (stage.val + 1)) C .uncapped accounting
              (MaxSelector.rule childSelector.choose (input.freshSuffix (stage.val + 1))
                (available.erase tool) (2 * controllerBadRisk risk (controllerTarget risk depth)) none)
              (Measure.dirac ()) ≤ ENNReal.ofReal bound := by
  let childInput := input.freshSuffix (stage.val + 1)
  let childAvailable := available.erase tool
  have hshort : (I.freshSuffix (stage.val + 1)).stageCount < I.stageCount := by
    rw [I.freshSuffix_stageCount]
    have hs : stage.val < I.stageCount := stage.isLt
    omega
  have hcost := ih (I.freshSuffix (stage.val + 1)) childInput childAvailable childSelector hshort
  have hRank : errorRank (I.freshSuffix (stage.val + 1)).compatibility childAvailable = (depth : ℕ∞) :=
    hchildRank
  have hfinite : errorRank (I.freshSuffix (stage.val + 1)).compatibility childAvailable ≠ ⊤ := by
    rw [hRank]
    exact ENat.natCast_ne_top depth
  have hcoefficient : 0 < childInput.orderedCoefficient childAvailable :=
    childInput.orderedCoefficient_pos childAvailable hfinite
  obtain ⟨childCutoff, hchildCutoff, hchildCost⟩ := hcost depth hRank 1 (by norm_num)
  obtain ⟨numericBound, numericCutoff, hnumericBound, hnumericCutoff, hnumeric⟩ :=
    controllerTarget_scaledBadRisk_iteratedLog_cutoff depth hdepth 2 (by norm_num)
  have hchildBudget : Tendsto
      (fun risk : ℚ => ((2 * controllerBadRisk risk (controllerTarget risk depth) : ℚ) : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simpa only [Function.comp_def] using rationalRisk_cast_tendsto_zero.comp
      (scaled_controllerBadRisk_tendsto_zero depth hdepth 2 (by norm_num))
  have hsmall : ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      ((2 * controllerBadRisk risk (controllerTarget risk depth) : ℚ) : ℝ) < childCutoff :=
    hchildBudget.eventually (eventually_lt_nhds hchildCutoff)
  obtain ⟨inputCutoff, hinputCutoff, hinput⟩ := rationalEventually_positive_cutoff hsmall
  refine ⟨2 * childInput.orderedCoefficient childAvailable * numericBound,
    min numericCutoff inputCutoff, by positivity, lt_min hnumericCutoff hinputCutoff, ?_⟩
  intro risk hrisk hquarter hcutoff C hcurrent accounting
  let badRisk := controllerBadRisk risk (controllerTarget risk depth)
  have hbadBounds := controllerBadRisk_bounds risk (controllerTarget risk depth) hrisk hquarter
    (controllerTarget_pos risk depth) (controllerTarget_le_quarter risk depth)
  have hbadPositive : 0 < badRisk := controllerBadRisk_positive risk (controllerTarget risk depth)
    hrisk hquarter (controllerTarget_pos risk depth) (controllerTarget_le_quarter risk depth)
  have hbudget : 0 < 2 * badRisk := by positivity
  have hbudgetSmall : 2 * badRisk ≤ 1 / 2 := by dsimp [badRisk]; linarith [hbadBounds.2]
  have hchildSmall : ((2 * badRisk : ℚ) : ℝ) < childCutoff :=
    hinput risk hrisk (hcutoff.trans_le (min_le_right _ _))
  have hnum := hnumeric risk hrisk (hcutoff.trans_le (min_le_left _ _))
  have hb := hchildCost (2 * badRisk) hbudget hbudgetSmall hchildSmall C hcurrent accounting
  have hp : (0 : ℝ) ≤ (controllerTarget risk depth : ℝ) := by
    exact_mod_cast (controllerTarget_pos risk depth).le
  change ENNReal.ofReal (controllerTarget risk depth : ℝ) *
    expectedBill childInput C .uncapped accounting
      (MaxSelector.rule childSelector.choose childInput childAvailable (2 * badRisk) none) (Measure.dirac ()) ≤ _
  calc
    _ ≤ ENNReal.ofReal (controllerTarget risk depth : ℝ) *
        ENNReal.ofReal ((1 + 1) * childInput.orderedCoefficient childAvailable *
          iteratedLog depth ((2 * badRisk : ℚ) : ℝ)⁻¹) := mul_le_mul' le_rfl hb
    _ = ENNReal.ofReal ((2 * childInput.orderedCoefficient childAvailable) *
        ((controllerTarget risk depth : ℝ) * iteratedLog depth (1 / ((2 * badRisk : ℚ) : ℝ)))) := by
      rw [← ENNReal.ofReal_mul hp]
      congr 1
      simp only [one_div]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hnum.2.2 (by positivity))

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Asymptotics
