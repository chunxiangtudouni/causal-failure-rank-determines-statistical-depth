module

public import PaperProofs.Common.ReferenceCostRecursion
public import PaperProofs.Common.FreshCoefficient
public import PaperProofs.Statistics.BadRiskAsymptotics
public import PaperProofs.Statistics.IteratedLogComparison

/-!
Actual-cost steps of the B18 strictly-shorter-suffix induction.
All numerical risk functions and actual expected bills are unchanged.
An induction hypothesis below ranges only over STRICTLY SHORTER inputs;
it is not an additional paper assumption or a bad-child O(1) premise.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PaperProofs.Common.Native

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

/-- Convergence of a real numerical allowance on the original risk scale
gives its original positive-real cutoff, without taking toReal of a bill. -/
theorem rationalRisk_cutoff_of_ratio_limit (depth : ℕ) (allowance : ℚ → ℝ)
    (limit upper : ℝ) (hlimit : limit < upper)
    (hconverges : Tendsto (fun risk : ℚ => allowance risk / iteratedLog depth (1 / (risk : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 limit)) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ risk : ℚ, 0 < risk → (risk : ℝ) < cutoff →
      allowance risk ≤ upper * iteratedLog depth (1 / (risk : ℝ)) := by
  have hratio := hconverges.eventually (eventually_lt_nhds hlimit)
  have hpositive : ∀ᶠ risk : ℚ in nhdsWithin 0 (Set.Ioi 0),
      0 < iteratedLog depth (1 / (risk : ℝ)) := by
    exact ((iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop).eventually
      (eventually_gt_atTop 0)
  apply rationalEventually_positive_cutoff
  filter_upwards [hratio, hpositive] with risk hr hp
  exact ((div_lt_iff₀ hp).mp hr).le

/-- The original actual local test is charged by its sharp posterior-SPRT
allowance at the exact target returned by the visible-history parser. -/
theorem referenceEntryLocalObservationPrice_le_sharp
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : referenceAvailableEntryTarget input available budget history = some p) :
    referenceEntryLocalObservationPrice input available budget stage history ≤
      ENNReal.ofReal ((input.experiment stage).coefficient *
        (Real.log (1 / (p : ℝ)) + (input.experiment stage).logIncrementBound true +
          2 * |Real.log ((input.experiment stage).priorReal true /
            (input.experiment stage).priorReal false)|)) := by
  let E := input.experiment stage
  have hp := referenceAvailableEntryTarget_valid input available budget p history htarget
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.1
  have hpone : (p : ℝ) ≤ 1 := by
    exact_mod_cast hp.2.trans (by norm_num : (1 / 4 : ℚ) ≤ 1)
  have hlog : 0 ≤ Real.log (1 / (p : ℝ)) :=
    Real.log_nonneg ((le_div_iff₀ hpR).mpr (by simpa only [one_mul] using hpone))
  have hB : 0 ≤ Real.log (1 / (p : ℝ)) + E.logIncrementBound true +
      2 * |Real.log (E.priorReal true / E.priorReal false)| := by
    have hK := E.logIncrementBound_nonneg true
    positivity
  have hb := E.bayesObservationCharge_le_drift_bound (Measure.dirac ()) (E.posteriorSPRT p)
    _ hB (E.posteriorSPRT_expectedObservationCharge_finite p
      (BinaryExperiment.posteriorThreshold_nonneg p hp.1 hp.2))
    (fun x => by simpa only [add_assoc] using E.posteriorSPRT_sharpObservationCharge p hp.1 hp.2 x)
  simpa only [referenceEntryLocalObservationPrice, htarget] using hb

/-- Infinite rank removes actual paid observations on every run, including
all failed paths and every private seed law. It does not discard correction
charges or assert that the full bill is zero. -/
theorem referenceExpectedObservationBill_infiniteRank {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤)
    (limit : ReferenceObservationLimit I) (ν : Measure Seed) :
    expectedObservationBill input C .uncapped accounting
      (referenceRule input available budget limit) ν = 0 := by
  have hlegal := referenceRule_uncapped_legal (Seed := Seed) input C hearly accounting available budget limit
  have hzero (stage : I.Stage) (sample : Seed × input.World) :
      runStageObservationBill input C .uncapped accounting
        (referenceRule input available budget limit) stage sample = 0 := by
    unfold runStageObservationBill
    apply le_antisymm (iSup_le fun n => ?_) bot_le
    obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting
      (referenceRule input available budget limit) hlegal sample n
    have hz := prefix_reference_reviews_zero_of_infinite_rank input C hearly accounting
      available budget hbudget hsmall htop limit sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp stage
    simp [hz]
  rw [expectedObservationBill_eq_sum_stage input C .uncapped accounting _ hlegal
    (measurable_referenceRule input available budget limit)]
  simp only [hzero, lintegral_zero, Finset.sum_const_zero]

theorem referenceExpectedBill_infiniteRank_le_corrections
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤) :
    expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  have hbill := expectedBill_le_observation_add input C .uncapped accounting
    (referenceIdealPolicy input C hearly accounting available budget) (Measure.dirac ())
  change expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
    expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) + _ at hbill
  rw [referenceExpectedObservationBill_infiniteRank input C hearly accounting available budget
    hbudget hsmall htop none (Measure.dirac ()), zero_add] at hbill
  exact hbill

/-- The original bad-child assertion follows from the genuine strictly
shorter-input cost induction hypothesis. The bound is uniform in every
original contract and normal-accounting function, charges the child's full
actual bill, and uses precisely the parser restart budget 2r'. -/
theorem referenceBadBranchCostBound_of_shorter_cost
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J), J.stageCount < I.stageCount →
      ReferenceCostAsymptotics child) :
    ReferenceBadBranchCostBound input := by
  intro stage available depth hdepth _hbad tool _htool hchildRank
  let childInput := input.freshSuffix (stage.val + 1)
  let childAvailable := available.erase tool
  have hshort : (I.freshSuffix (stage.val + 1)).stageCount < I.stageCount := by
    rw [I.freshSuffix_stageCount]
    have hs : stage.val < I.stageCount := stage.isLt
    omega
  have hcost := ih (I.freshSuffix (stage.val + 1)) childInput hshort
  have hRank : errorRank (I.freshSuffix (stage.val + 1)).compatibility childAvailable = (depth : ℕ∞) :=
    hchildRank
  have hfinite : errorRank (I.freshSuffix (stage.val + 1)).compatibility childAvailable ≠ ⊤ := by
    rw [hRank]
    exact ENat.natCast_ne_top depth
  have hcoefficient : 0 < childInput.orderedCoefficient childAvailable :=
    childInput.orderedCoefficient_pos childAvailable hfinite
  obtain ⟨childCutoff, hchildCutoff, hchildCost⟩ := hcost childAvailable depth hRank 1 (by norm_num)
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
  intro risk hrisk hquarter hcutoff
  dsimp only
  intro C hcurrent accounting
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
      (referenceIdealPolicy childInput C hcurrent.1 accounting childAvailable (2 * badRisk)).rule (Measure.dirac ()) ≤ _
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

/-- A proved ACTUAL parent-cost induction step. Its bad-child term has
already been discharged from strictly shorter cost induction, not supplied
as an O(1) premise. Only the unchanged good-child cost remains to compare
with the parent's iterated-log scale. Every original correction is charged. -/
theorem referenceExpectedBill_finiteBad_step_of_shorter_cost
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J), J.stageCount < I.stageCount →
      ReferenceCostAsymptotics child)
    (available : Finset I.Tool) (first nextStage : I.Stage)
    (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (depth : ℕ+) (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad depth)) :
    ∃ (tool : I.Tool) (bound cutoff : ℝ),
      referenceAvailableRepairTool I available first ∅ = some tool ∧
      tool ∈ I.eligible first ∩ available ∧ 0 ≤ bound ∧ 0 < cutoff ∧
      ∀ (budget : ℚ), 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        ∀ (C : Contract I) (_hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I),
        expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
          (referenceEntryLocalObservationPrice input available budget first [] +
            (referenceFreshChildObservationCost input nextStage available (budget / 2) + ENNReal.ofReal bound)) +
            (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  obtain ⟨tool, hpick⟩ := referenceAvailableRepairTool_exists_finiteBad available first depth hkind
  have htool := referenceAvailableRepairTool_spec I available first ∅ tool hpick
  have hsem := referenceAvailableRankCase_semantics I available first ∅ (.finiteBad depth) hkind
  simp only [Finset.sdiff_empty] at htool hsem
  have hchild := htool.2.trans hsem.2
  obtain ⟨bound, cutoff, hbound, hcutoff, hbadCost⟩ :=
    referenceBadBranchCostBound_of_shorter_cost input ih first available depth.val
      (by have := depth.pos; omega) hsem.2 tool htool.1 hchild
  refine ⟨tool, bound, cutoff, hpick, htool.1, hbound, hcutoff, ?_⟩
  intro budget hbudget hsmall hcut C hcurrent accounting
  have hrisk : 0 < budget / 2 := by linarith
  have hquarter : budget / 2 ≤ 1 / 4 := by linarith
  have hbR : (0 : ℝ) < (budget : ℝ) := by exact_mod_cast hbudget
  have hcutHalf : ((budget / 2 : ℚ) : ℝ) < cutoff := by push_cast; linarith
  have hbad := hbadCost (budget / 2) hrisk hquarter hcutHalf
  dsimp only at hbad
  have hfull := hbad (currentRelaxedContract (I.freshSuffix (first.val + 1)))
    ⟨rfl, rfl⟩ (zeroNormalAccounting (I.freshSuffix (first.val + 1)))
  let childBudget := 2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val)
  let childFullCost (index : ℕ) : ℝ≥0∞ :=
    expectedBill (input.freshSuffix index) (currentRelaxedContract (I.freshSuffix index)) .uncapped
      (zeroNormalAccounting (I.freshSuffix index))
      (referenceRule (input.freshSuffix index) (available.erase tool) childBudget none) (Measure.dirac ())
  change ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) *
    childFullCost (first.val + 1) ≤ ENNReal.ofReal bound at hfull
  have hindex : first.val + 1 = nextStage.val := by omega
  rw [hindex] at hfull
  let childInput := input.freshSuffix nextStage.val
  let childC := currentRelaxedContract (I.freshSuffix nextStage.val)
  let childAccounting := zeroNormalAccounting (I.freshSuffix nextStage.val)
  have hobservation : ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) *
      referenceFreshChildObservationCost input nextStage (available.erase tool) childBudget ≤ ENNReal.ofReal bound := by
    apply (mul_le_mul' le_rfl (expectedObservationBill_le_actual childInput childC .uncapped childAccounting
      (referenceIdealPolicy childInput childC rfl childAccounting (available.erase tool) childBudget).rule
      (Measure.dirac ()))).trans hfull
  have hparent := referenceExpectedObservationBill_finiteBad_le input C hcurrent accounting available budget
    hbudget hsmall first nextStage hfirst hnext depth hkind tool hpick
  have hbill := expectedBill_le_observation_add input C .uncapped accounting
    (referenceIdealPolicy input C hcurrent.1 accounting available budget) (Measure.dirac ())
  exact hbill.trans (add_le_add (hparent.trans
    (add_le_add le_rfl (add_le_add le_rfl hobservation))) le_rfl)

/-- The actual good-child observation charge is bounded by the original
strictly-shorter cost induction hypothesis at its exact half budget. -/
theorem referenceFreshChildObservationCost_finite_of_shorter_cost
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J), J.stageCount < I.stageCount →
      ReferenceCostAsymptotics child)
    (stage : I.Stage) (hstage : 0 < stage.val) (available : Finset I.Tool) (depth : ℕ)
    (hrank : errorRank (I.freshSuffix stage.val).compatibility available = (depth : ℕ∞))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ (budget : ℚ), 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        referenceFreshChildObservationCost input stage available (budget / 2) ≤
          ENNReal.ofReal ((1 + epsilon) * (input.freshSuffix stage.val).orderedCoefficient available *
            iteratedLog depth (1 / ((budget / 2 : ℚ) : ℝ))) := by
  have hshort : (I.freshSuffix stage.val).stageCount < I.stageCount := by
    rw [I.freshSuffix_stageCount]
    have hs : stage.val < I.stageCount := stage.isLt
    omega
  obtain ⟨cutoff, hcutoff, hcost⟩ :=
    ih (I.freshSuffix stage.val) (input.freshSuffix stage.val) hshort available depth hrank epsilon hepsilon
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
    (referenceRule (input.freshSuffix stage.val) available (budget / 2) none) (Measure.dirac ()) ≤ _ at hactual
  exact (expectedObservationBill_le_actual (input.freshSuffix stage.val)
    (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
    (zeroNormalAccounting (I.freshSuffix stage.val))
    (referenceRule (input.freshSuffix stage.val) available (budget / 2) none) (Measure.dirac ())).trans
      (by simpa only [one_div] using hactual)

/-- The no-tool parent step retains the actual good-child charge and all
corrections. Failed no-tool reports contribute no fictitious child run. -/
theorem referenceExpectedBill_noTool_step
    (input : StatisticalInput I) (available : Finset I.Tool) (first nextStage : I.Stage)
    (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (hkind : referenceAvailableRankCase I available first ∅ = some .noTool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I) :
    expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      (referenceEntryLocalObservationPrice input available budget first [] +
        referenceFreshChildObservationCost input nextStage available (budget / 2)) +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  have hparent := referenceExpectedObservationBill_noTool_le input C hcurrent accounting available budget
    hbudget hsmall first nextStage hfirst hnext hkind
  have hbill := expectedBill_le_observation_add input C .uncapped accounting
    (referenceIdealPolicy input C hcurrent.1 accounting available budget) (Measure.dirac ())
  exact hbill.trans (add_le_add hparent le_rfl)

/-- The actual finite-bad head price has exactly the critical-head leading
coefficient and an arbitrarily small allowance on the parent's scale. -/
theorem referenceEntryLocalObservationPrice_finiteBad_asymptotic
    (input : StatisticalInput I) (available : Finset I.Tool) (first : I.Stage)
    (hfirst : first.val = 0) (badDepth : ℕ+)
    (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad badDepth))
    (depth : ℕ) (hdepth : 1 ≤ depth) (horder : depth ≤ badDepth.val + 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 →
      (budget : ℝ) < cutoff →
      referenceEntryLocalObservationPrice input available budget first [] ≤
        ENNReal.ofReal (((input.experiment first).coefficient *
          (if depth = badDepth.val + 1 then 1 else 0) + eta) *
          iteratedLog depth (1 / (budget : ℝ))) := by
  let E := input.experiment first
  let offset := E.logIncrementBound true + 2 * |Real.log (E.priorReal true / E.priorReal false)|
  let allowance := fun budget : ℚ => E.coefficient *
    (Real.log (1 / (controllerTarget (budget / 2) badDepth.val : ℝ)) + offset)
  have hlimit := controllerTarget_half_price_div_iteratedLog badDepth.val depth
    (by have := badDepth.pos; omega) hdepth horder E.coefficient offset
  obtain ⟨cutoff, hcutoff, hnum⟩ := rationalRisk_cutoff_of_ratio_limit depth allowance
    _ (E.coefficient * (if depth = badDepth.val + 1 then 1 else 0) + eta) (by linarith) hlimit
  refine ⟨cutoff, hcutoff, ?_⟩
  intro budget hbudget hsmall hcut
  have htarget : referenceAvailableEntryTarget input available budget [] =
      some (controllerTarget (budget / 2) badDepth.val) :=
    referenceAvailableEntryTarget_initial input available budget hbudget hsmall first hfirst (.finiteBad badDepth) hkind
  have hsharp := referenceEntryLocalObservationPrice_le_sharp input available budget first [] _ htarget
  have hallowance : referenceEntryLocalObservationPrice input available budget first [] ≤
      ENNReal.ofReal (allowance budget) := by
    simpa only [allowance, offset, E, add_assoc] using hsharp
  exact hallowance.trans (ENNReal.ofReal_le_ofReal (hnum budget hbudget hcut))

/-- A finite good child contributes its original coefficient iff its rank
equals the parent's. All higher good-child ranks are negligible, directly
from the strictly shorter cost induction hypothesis and original half risk. -/
theorem referenceFreshChildObservationCost_asymptotic_of_shorter_cost
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J), J.stageCount < I.stageCount →
      ReferenceCostAsymptotics child)
    (stage : I.Stage) (hstage : 0 < stage.val) (available : Finset I.Tool)
    (goodDepth depth : ℕ) (hdepth : 1 ≤ depth) (horder : depth ≤ goodDepth)
    (hrank : errorRank (I.freshSuffix stage.val).compatibility available = (goodDepth : ℕ∞))
    (eta : ℝ) (heta : 0 < eta) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 →
      (budget : ℝ) < cutoff →
      referenceFreshChildObservationCost input stage available (budget / 2) ≤
        ENNReal.ofReal (((if goodDepth = depth then
          (input.freshSuffix stage.val).orderedCoefficient available else 0) + eta) *
          iteratedLog depth (1 / (budget : ℝ))) := by
  let coefficient := (input.freshSuffix stage.val).orderedCoefficient available
  have hcoefficient : 0 < coefficient :=
    (input.freshSuffix stage.val).orderedCoefficient_pos available (by rw [hrank]; exact ENat.natCast_ne_top goodDepth)
  let childEpsilon := eta / (2 * coefficient)
  have hchildEpsilon : 0 < childEpsilon := by dsimp [childEpsilon]; positivity
  obtain ⟨childCutoff, hchildCutoff, hchild⟩ := referenceFreshChildObservationCost_finite_of_shorter_cost
    input ih stage hstage available goodDepth hrank childEpsilon hchildEpsilon
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

theorem rationalRisk_constant_cutoff (depth : ℕ) (constant eta : ℝ) (heta : 0 < eta) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ budget : ℚ, 0 < budget → (budget : ℝ) < cutoff →
      constant ≤ eta * iteratedLog depth (1 / (budget : ℝ)) := by
  exact rationalRisk_cutoff_of_ratio_limit depth (fun _ => constant) 0 eta heta
    (tendsto_const_nhds.div_atTop ((iteratedLog_tendsto_atTop depth).comp rationalInverse_tendsto_atTop))

theorem rationalRisk_log_scale_price_div_iteratedLog_one (scale : ℝ) (hscale : 0 < scale)
    (coefficient offset : ℝ) :
    Tendsto (fun budget : ℚ => coefficient * (Real.log (scale / (budget : ℝ)) + offset) /
      iteratedLog 1 (1 / (budget : ℝ))) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 coefficient) := by
  have hden := (iteratedLog_tendsto_atTop 1).comp rationalInverse_tendsto_atTop
  have hnegligible : Tendsto (fun budget : ℚ => (Real.log scale + offset) /
      iteratedLog 1 (1 / (budget : ℝ))) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hmain : Tendsto (fun budget : ℚ => coefficient *
      (1 + (Real.log scale + offset) / iteratedLog 1 (1 / (budget : ℝ))))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 coefficient) := by
    simpa only [add_zero, mul_one] using
      ((show Tendsto (fun _ : ℚ => (1 : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1)
        from tendsto_const_nhds).add hnegligible).const_mul coefficient
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin, hden.eventually_ne_atTop 0] with budget hbudget hne
  have hbR : (0 : ℝ) < (budget : ℝ) := by exact_mod_cast hbudget
  have hinverse : 1 / (budget : ℝ) ≠ 0 := (one_div_pos.mpr hbR).ne'
  change coefficient * (1 + (Real.log scale + offset) / Real.log (1 / (budget : ℝ))) =
    coefficient * (Real.log (scale / (budget : ℝ)) + offset) / Real.log (1 / (budget : ℝ))
  rw [div_eq_mul_one_div scale, Real.log_mul hscale.ne' hinverse]
  change Real.log (1 / (budget : ℝ)) ≠ 0 at hne
  field_simp
  ring

/-- The actual no-tool local charge has its original local KL coefficient
on the rank-one scale; the global finite allowance is used only as a proved
upper bound for the unchanged test. -/
theorem referenceEntryLocalObservationPrice_noTool_asymptotic
    (input : StatisticalInput I) (available : Finset I.Tool) (first : I.Stage)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 →
      (budget : ℝ) < cutoff →
      referenceEntryLocalObservationPrice input available budget first [] ≤
        ENNReal.ofReal (((input.experiment first).coefficient + eta) *
          iteratedLog 1 (1 / (budget : ℝ))) := by
  let E := input.experiment first
  let offset := E.logIncrementBound true + 2 * |Real.log (E.priorReal true / E.priorReal false)|
  let allowance := fun budget : ℚ => E.coefficient *
    (Real.log ((referenceQuotaConstant I.stageCount : ℝ) / (budget : ℝ)) + offset)
  have hscale : (0 : ℝ) < (referenceQuotaConstant I.stageCount : ℝ) := by
    unfold referenceQuotaConstant
    positivity
  have hlimit := rationalRisk_log_scale_price_div_iteratedLog_one
    (referenceQuotaConstant I.stageCount : ℝ) hscale E.coefficient offset
  obtain ⟨cutoff, hcutoff, hnum⟩ := rationalRisk_cutoff_of_ratio_limit 1 allowance E.coefficient
    (E.coefficient + eta) (by linarith) hlimit
  refine ⟨cutoff, hcutoff, ?_⟩
  intro budget hbudget hsmall hcut
  have hglobal := referenceEntryLocalObservationPrice_le_global input available budget hbudget hsmall first []
  have hallowance : referenceEntryLocalObservationPrice input available budget first [] ≤
      ENNReal.ofReal (allowance budget) := by
    simpa only [referenceGlobalStageObservationPrice, allowance, offset, E, add_assoc] using hglobal
  exact hallowance.trans (ENNReal.ofReal_le_ofReal (hnum budget hbudget hcut))

/-- The good-child leading term also covers independently infinite rank,
where the actual observation cost is exactly zero. -/
theorem referenceFreshChildObservationCost_head_asymptotic
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J), J.stageCount < I.stageCount →
      ReferenceCostAsymptotics child)
    (stage : I.Stage) (hstage : 0 < stage.val) (available : Finset I.Tool)
    (depth : ℕ) (hdepth : 1 ≤ depth)
    (horder : (depth : ℕ∞) ≤ errorRank (I.freshSuffix stage.val).compatibility available)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 →
      (budget : ℝ) < cutoff →
      referenceFreshChildObservationCost input stage available (budget / 2) ≤
        ENNReal.ofReal (((if errorRank (I.freshSuffix stage.val).compatibility available = (depth : ℕ∞) then
          (input.freshSuffix stage.val).orderedCoefficient available else 0) + eta) *
          iteratedLog depth (1 / (budget : ℝ))) := by
  by_cases htop : errorRank (I.freshSuffix stage.val).compatibility available = ⊤
  · refine ⟨1, by norm_num, ?_⟩
    intro budget hbudget hsmall _
    have hhalf : 0 < budget / 2 := by linarith
    have hhalfSmall : budget / 2 ≤ 1 / 2 := by linarith
    unfold referenceFreshChildObservationCost
    rw [referenceExpectedObservationBill_infiniteRank (input.freshSuffix stage.val)
      (currentRelaxedContract (I.freshSuffix stage.val)) rfl (zeroNormalAccounting (I.freshSuffix stage.val))
      available (budget / 2) hhalf hhalfSmall htop none (Measure.dirac ())]
    exact bot_le
  · obtain ⟨goodDepth, hgood⟩ := ENat.ne_top_iff_exists.mp htop
    have horderNat : depth ≤ goodDepth := by
      exact ENat.natCast_le_natCast.mp (hgood ▸ horder)
    have hbound := referenceFreshChildObservationCost_asymptotic_of_shorter_cost input ih stage hstage
      available goodDepth depth hdepth horderNat hgood.symm eta heta
    simpa only [← hgood, ENat.natCast_inj] using hbound

/-- Adding the two actual observation allowances and the fixed bad/correction
allowance takes place in ENNReal. Only the proved finite correction constant
is converted to a real number; actual bills are never converted. -/
theorem ennreal_parent_three_allowances
    (headPrice good corrections : ℝ≥0∞) (bound localLead goodLead eta scale : ℝ)
    (hcorrections : corrections ≠ ⊤) (hbound : 0 ≤ bound)
    (hlocalLead : 0 ≤ localLead) (hgoodLead : 0 ≤ goodLead) (heta : 0 < eta)
    (hlocal : headPrice ≤ ENNReal.ofReal ((localLead + eta) * scale))
    (hgood : good ≤ ENNReal.ofReal ((goodLead + eta) * scale))
    (hconstant : bound + corrections.toReal ≤ eta * scale) :
    (headPrice + (good + ENNReal.ofReal bound)) + corrections ≤
      ENNReal.ofReal ((localLead + goodLead + 3 * eta) * scale) := by
  have hc : 0 ≤ corrections.toReal := ENNReal.toReal_nonneg
  have hscale : 0 ≤ scale := by nlinarith
  have hx : 0 ≤ (localLead + eta) * scale := mul_nonneg (by linarith) hscale
  have hy : 0 ≤ (goodLead + eta) * scale := mul_nonneg (by linarith) hscale
  have hz : 0 ≤ eta * scale := mul_nonneg heta.le hscale
  have hfixed : ENNReal.ofReal bound + corrections ≤ ENNReal.ofReal (eta * scale) := by
    calc
      _ = ENNReal.ofReal (bound + corrections.toReal) := by
        rw [ENNReal.ofReal_add hbound hc, ENNReal.ofReal_toReal hcorrections]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hconstant
  calc
    _ = (headPrice + good) + (ENNReal.ofReal bound + corrections) := by ac_rfl
    _ ≤ (ENNReal.ofReal ((localLead + eta) * scale) + ENNReal.ofReal ((goodLead + eta) * scale)) +
        ENNReal.ofReal (eta * scale) := add_le_add (add_le_add hlocal hgood) hfixed
    _ = ENNReal.ofReal (((localLead + eta) * scale + (goodLead + eta) * scale) + eta * scale) := by
      rw [ENNReal.ofReal_add (add_nonneg hx hy) hz, ENNReal.ofReal_add hx hy]
    _ = _ := by congr 1; ring

/-- Epsilon assembly for an actual initial-step cost recurrence. The two
recurrence/price arguments are proved from the unchanged controller below;
this lemma supplies no cost or risk assumption to the final result. -/
theorem referenceCostAsymptotics_initial_step_of_bounds
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J), J.stageCount < I.stageCount →
      ReferenceCostAsymptotics child)
    (available : Finset I.Tool) (first nextStage : I.Stage) (hnext : 0 < nextStage.val)
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
        expectedBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
          (referenceEntryLocalObservationPrice input available budget first [] +
            (referenceFreshChildObservationCost input nextStage available (budget / 2) + ENNReal.ofReal bound)) +
            (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ budget : ℚ, 0 < budget → budget ≤ 1 / 2 → (budget : ℝ) < cutoff →
        ∀ (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I),
          expectedBill input C .uncapped accounting
            (referenceIdealPolicy input C hcurrent.1 accounting available budget).rule (Measure.dirac ()) ≤
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
  obtain ⟨goodCutoff, hgoodCutoff, hgood⟩ := referenceFreshChildObservationCost_head_asymptotic
    input ih nextStage hnext available depth hdepth hgoodOrder eta heta
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
    (referenceFreshChildObservationCost input nextStage available (budget / 2)) corrections
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
          (referenceFreshChildObservationCost input nextStage available (budget / 2) + ENNReal.ofReal bound)) +
          corrections := hstep budget hbudget hsmall hstepCut C hcurrent accounting
    _ ≤ ENNReal.ofReal ((localLead + goodLead + 3 * eta) *
        iteratedLog depth (1 / (budget : ℝ))) := hparts
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      simpa only [one_div] using mul_le_mul_of_nonneg_right hcoefficientAllowance hscale)

/-- The complete actual-cost induction step. Every price and recurrence
argument of the epsilon assembly is discharged from the original controller,
independent rank, original coefficient, and strictly shorter suffix induction. -/
theorem referenceCostAsymptotics_of_shorter_cost
    (input : StatisticalInput I)
    (ih : ∀ (J : Instance) (child : StatisticalInput J), J.stageCount < I.stageCount →
      ReferenceCostAsymptotics child) :
    ReferenceCostAsymptotics input := by
  by_cases hsmallSize : I.stageCount ≤ 1
  · exact (referenceCostClaims_atMostOne input hsmallSize).1
  intro available depth hrank
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
    apply referenceCostAsymptotics_initial_step_of_bounds input ih available first nextStage
      (by simp only [hnext]; norm_num) 1 (by norm_num) hrank hgoodOrder
      (input.experiment first).coefficient (input.experiment first).coefficient_pos.le hcoefficient
      0 1 (by norm_num) (by norm_num)
      (referenceEntryLocalObservationPrice_noTool_asymptotic input available first)
    intro budget hbudget hsmall _ C hcurrent accounting
    simpa only [ENNReal.ofReal_zero, add_zero] using
      referenceExpectedBill_noTool_step input available first nextStage hfirst hnext hkind
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
      referenceExpectedBill_finiteBad_step_of_shorter_cost input ih available first nextStage hfirst hnext badDepth hkind
    exact referenceCostAsymptotics_initial_step_of_bounds input ih available first nextStage
      (by simp only [hnext]; norm_num) depth hdepth hrank hgoodOrder localLead hlocalLead hcoefficient
      bound stepCutoff hbound hstepCutoff
      (referenceEntryLocalObservationPrice_finiteBad_asymptotic input available first hfirst badDepth hkind depth hdepth horderBad)
      hstep

/-- B18's original rank-sensitive actual expected-bill asymptotics, for every
original input and finite available rank. The induction parameter is strictly
decreasing fresh-suffix stage count; no child performance is assumed. -/
theorem referenceCostAsymptotics (input : StatisticalInput I) :
    ReferenceCostAsymptotics input := by
  have hall : ∀ n : ℕ, ∀ (J : Instance) (child : StatisticalInput J),
      J.stageCount = n → ReferenceCostAsymptotics child := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J child hsize
      apply referenceCostAsymptotics_of_shorter_cost child
      intro K grandchild hshort
      exact ih K.stageCount (by omega) K grandchild rfl
  exact hall I.stageCount I input rfl

/-- Both unchanged B18 expected-cost obligations, including the uniformly
bounded probability-weighted actual bad child at the original parser risk. -/
theorem referenceCostClaims (input : StatisticalInput I) : ReferenceCostClaims input := by
  refine ⟨referenceCostAsymptotics input, referenceBadBranchCostBound_of_shorter_cost input ?_⟩
  intro J child _
  exact referenceCostAsymptotics child

end PaperProofs.Common.Native
