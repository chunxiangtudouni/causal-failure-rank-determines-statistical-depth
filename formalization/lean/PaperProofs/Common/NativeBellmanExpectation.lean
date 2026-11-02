module

public import PaperProofs.Common.NativeBellmanWorldSplit
public import PaperProofs.Common.NativeBellmanPrivateSeeds
public import PaperProofs.Common.HistorySuffixBridge
public import PaperProofs.Common.NativeHeadBayes
public import PaperProofs.Common.NativeBellmanChargeUpper

/-!
Tonelli factorization of head-selected child charges in the original
Bellman construction. Selection reads only the local seed and head world;
each child reads its own independent seed and the original fresh suffix.
Nonnegative costs may be infinite throughout.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.BellmanExpectation

open PaperProofs.Statistics BellmanPrivateSeeds

attribute [local instance] Classical.propDecidable

section ProductReorder

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

theorem measurePreserving_middleSwap (μ : Measure A) (ν : Measure B) (ξ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ξ] :
    MeasurePreserving (fun pair : (A × B) × C => ((pair.1.1, pair.2), pair.1.2))
      ((μ.prod ν).prod ξ) ((μ.prod ξ).prod ν) := by
  have h1 := measurePreserving_prodAssoc μ ν ξ
  have h2 := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := ξ))
  have h3 := MeasurePreserving.symm
    (MeasurableEquiv.prodAssoc : (A × C) × B ≃ᵐ A × C × B)
    (measurePreserving_prodAssoc μ ξ ν)
  have h := h3.comp (h2.comp h1)
  exact h

theorem measurePreserving_pairShuffle (μ : Measure A) (ν : Measure B)
    (ξ : Measure C) (τ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ξ] [SFinite τ] :
    MeasurePreserving (fun pair : (A × B) × (C × D) =>
      ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2)))
      ((μ.prod ν).prod (ξ.prod τ)) ((μ.prod ξ).prod (ν.prod τ)) := by
  have h1 := MeasurePreserving.symm
    (MeasurableEquiv.prodAssoc : ((A × B) × C) × D ≃ᵐ (A × B) × C × D)
    (measurePreserving_prodAssoc (μ.prod ν) ξ τ)
  have h2 := (measurePreserving_middleSwap μ ν ξ).prod (MeasurePreserving.id τ)
  have h3 := measurePreserving_prodAssoc (μ.prod ξ) ν τ
  exact h3.comp (h2.comp h1)

end ProductReorder

section JointLaw

variable {I : Instance} {Seed Local Child : Type*}
variable [MeasurableSpace Seed] [MeasurableSpace Local] [MeasurableSpace Child]

def headChildSplit (input : StatisticalInput I) (head : I.Stage)
    (localSeed : Seed → Local) (childSeed : Seed → Child) (sample : Seed × input.World) :
    (Local × input.StageSample head) × (Child × (input.freshSuffix 1).World) :=
  ((localSeed sample.1, sample.2 head), (childSeed sample.1, input.restrictFreshWorld 1 sample.2))

theorem measurable_headChildSplit (input : StatisticalInput I) (head : I.Stage)
    (localSeed : Seed → Local) (childSeed : Seed → Child)
    (hlocal : Measurable localSeed) (hchild : Measurable childSeed) :
    Measurable (headChildSplit input head localSeed childSeed) :=
  ((hlocal.comp measurable_fst).prodMk ((measurable_pi_apply head).comp measurable_snd)).prodMk
    ((hchild.comp measurable_fst).prodMk ((input.measurable_restrictFreshWorld 1).comp measurable_snd))

theorem headChildSplit_law (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (ν : Measure Seed) (localLaw : Measure Local) (childLaw : Measure Child)
    [SFinite localLaw] [SFinite childLaw]
    (localSeed : Seed → Local) (childSeed : Seed → Child)
    (hlocal : Measurable localSeed) (hchild : Measurable childSeed)
    (hseeds : ν.map (fun seed => (localSeed seed, childSeed seed)) = localLaw.prod childLaw) :
    (input.seededWorldLaw ν).map (headChildSplit input head localSeed childSeed) =
      (localLaw.prod (input.stageLaw head)).prod (childLaw.prod (input.freshSuffix 1).worldLaw) := by
  have hworld : input.worldLaw.map (fun world => (world head, input.restrictFreshWorld 1 world)) =
      (input.stageLaw head).prod (input.freshSuffix 1).worldLaw := by
    rw [(bellmanHead_independent_freshSuffix input head hhead).map_prod_eq_prod_map_map
      (measurable_pi_apply head).aemeasurable (input.measurable_restrictFreshWorld 1).aemeasurable,
      input.worldLaw_coordinate, input.restrictFreshWorld_worldLaw]
  let split : Seed × input.World → (Local × Child) × (input.StageSample head × (input.freshSuffix 1).World) :=
    fun sample => ((localSeed sample.1, childSeed sample.1),
      (sample.2 head, input.restrictFreshWorld 1 sample.2))
  have hsplit : Measurable split :=
    ((hlocal.prodMk hchild).comp measurable_fst).prodMk
      (((measurable_pi_apply head).prodMk (input.measurable_restrictFreshWorld 1)).comp measurable_snd)
  have hmap : (input.seededWorldLaw ν).map split =
      (localLaw.prod childLaw).prod ((input.stageLaw head).prod (input.freshSuffix 1).worldLaw) := by
    have h := Measure.map_prod_map ν input.worldLaw (hlocal.prodMk hchild)
      ((measurable_pi_apply head).prodMk (input.measurable_restrictFreshWorld 1))
    rw [hseeds, hworld] at h
    exact h.symm
  let shuffle : (Local × Child) × (input.StageSample head × (input.freshSuffix 1).World) →
      (Local × input.StageSample head) × (Child × (input.freshSuffix 1).World) :=
    fun pair => ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2))
  have hshuffle := measurePreserving_pairShuffle localLaw childLaw
    (input.stageLaw head) (input.freshSuffix 1).worldLaw
  calc
    _ = ((input.seededWorldLaw ν).map split).map shuffle :=
      (Measure.map_map hshuffle.measurable hsplit).symm
    _ = _ := by rw [hmap]; exact hshuffle.map_eq

theorem selectedChild_integral (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (ν : Measure Seed) (localLaw : Measure Local) (childLaw : Measure Child)
    [SFinite localLaw] [SFinite childLaw]
    (localSeed : Seed → Local) (childSeed : Seed → Child)
    (hlocal : Measurable localSeed) (hchild : Measurable childSeed)
    (hseeds : ν.map (fun seed => (localSeed seed, childSeed seed)) = localLaw.prod childLaw)
    (gate : Set (Local × input.StageSample head)) (hgate : MeasurableSet gate)
    (cost : Child × (input.freshSuffix 1).World → ℝ≥0∞) (hcost : Measurable cost) :
    (∫⁻ sample, gate.indicator (fun _ => (1 : ℝ≥0∞)) (localSeed sample.1, sample.2 head) *
      cost (childSeed sample.1, referenceSuffixWorld input 1 sample.2) ∂input.seededWorldLaw ν) =
      (localLaw.prod (input.stageLaw head)) gate *
        ∫⁻ child, cost child ∂childLaw.prod (input.freshSuffix 1).worldLaw := by
  let f : (Local × input.StageSample head) × (Child × (input.freshSuffix 1).World) → ℝ≥0∞ :=
    fun pair => gate.indicator (fun _ => (1 : ℝ≥0∞)) pair.1 * cost pair.2
  have hg : Measurable (gate.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hgate
  have hf : Measurable f := (hg.comp measurable_fst).mul (hcost.comp measurable_snd)
  have hm := measurable_headChildSplit input head localSeed childSeed hlocal hchild
  have h := lintegral_map (μ := input.seededWorldLaw ν) hf hm
  rw [headChildSplit_law input head hhead ν localLaw childLaw localSeed childSeed hlocal hchild hseeds] at h
  have hprod := lintegral_prod_mul (μ := localLaw.prod (input.stageLaw head))
    (ν := childLaw.prod (input.freshSuffix 1).worldLaw) hg.aemeasurable hcost.aemeasurable
  have hi : (∫⁻ sample, gate.indicator (fun _ => (1 : ℝ≥0∞)) sample
      ∂localLaw.prod (input.stageLaw head)) = (localLaw.prod (input.stageLaw head)) gate := by
    exact lintegral_indicator_fun_one (μ := localLaw.prod (input.stageLaw head)) hgate
  rw [hi] at hprod
  calc
    _ = ∫⁻ sample, f (headChildSplit input head localSeed childSeed sample) ∂input.seededWorldLaw ν := by
      simp only [f, headChildSplit, referenceSuffixWorld_eq_restrictFreshWorld]
    _ = _ := h.symm.trans hprod

end JointLaw

section CombinedSelection

variable {I : Instance} {Local Good Bad : Type*}
variable [MeasurableSpace Local] [MeasurableSpace Good] [MeasurableSpace Bad]

theorem selectedBranches_integral (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (gate : Set (Local × input.StageSample head)) (hgate : MeasurableSet gate)
    (goodCost : Good × (input.freshSuffix 1).World → ℝ≥0∞) (hgoodCost : Measurable goodCost)
    (badCost : Bad × (input.freshSuffix 1).World → ℝ≥0∞) (hbadCost : Measurable badCost) :
    (∫⁻ sample, if (localSeed sample.1, sample.2 head) ∈ gate then
        goodCost (goodSeed sample.1, referenceSuffixWorld input 1 sample.2)
      else badCost (badSeed sample.1, referenceSuffixWorld input 1 sample.2)
      ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw)) =
      (localLaw.prod (input.stageLaw head)) gate *
          (∫⁻ child, goodCost child ∂goodLaw.prod (input.freshSuffix 1).worldLaw) +
        (localLaw.prod (input.stageLaw head)) gateᶜ *
          (∫⁻ child, badCost child ∂badLaw.prod (input.freshSuffix 1).worldLaw) := by
  classical
  let goodPart : CombinedSeed Local Good Bad × input.World → ℝ≥0∞ := fun sample =>
    gate.indicator (fun _ => (1 : ℝ≥0∞)) (localSeed sample.1, sample.2 head) *
      goodCost (goodSeed sample.1, referenceSuffixWorld input 1 sample.2)
  let badPart : CombinedSeed Local Good Bad × input.World → ℝ≥0∞ := fun sample =>
    gateᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (localSeed sample.1, sample.2 head) *
      badCost (badSeed sample.1, referenceSuffixWorld input 1 sample.2)
  have hm : Measurable goodPart := by
    dsimp only [goodPart]
    rw [show referenceSuffixWorld input 1 = input.restrictFreshWorld 1 from
      funext (referenceSuffixWorld_eq_restrictFreshWorld input 1)]
    exact ((measurable_const.indicator hgate).comp
      ((measurable_localSeed.comp measurable_fst).prodMk ((measurable_pi_apply head).comp measurable_snd))).mul
      (hgoodCost.comp ((measurable_goodSeed.comp measurable_fst).prodMk
        ((input.measurable_restrictFreshWorld 1).comp measurable_snd)))
  have hpoint : (fun sample : CombinedSeed Local Good Bad × input.World =>
      if (localSeed sample.1, sample.2 head) ∈ gate then
        goodCost (goodSeed sample.1, referenceSuffixWorld input 1 sample.2)
      else badCost (badSeed sample.1, referenceSuffixWorld input 1 sample.2)) =
      fun sample => goodPart sample + badPart sample := by
    funext sample
    by_cases hs : (localSeed sample.1, sample.2 head) ∈ gate <;>
      simp [goodPart, badPart, hs]
  rw [hpoint, lintegral_add_left hm]
  exact congrArg₂ (· + ·)
    (selectedChild_integral input head hhead (combinedLaw localLaw goodLaw badLaw) localLaw goodLaw
      localSeed goodSeed measurable_localSeed measurable_goodSeed
      (localGood_jointLaw localLaw goodLaw badLaw) gate hgate goodCost hgoodCost)
    (selectedChild_integral input head hhead (combinedLaw localLaw goodLaw badLaw) localLaw badLaw
      localSeed badSeed measurable_localSeed measurable_badSeed
      (localBad_jointLaw localLaw goodLaw badLaw) gateᶜ hgate.compl badCost hbadCost)

def headCorrectGate (input : StatisticalInput I) (head : I.Stage)
    (test : (input.experiment head).AdmissibleRule Local) : Set (Local × input.StageSample head) :=
  {sample | test.rule.decision sample.1 sample.2.2 = sample.2.1}

theorem measurableSet_headCorrectGate (input : StatisticalInput I) (head : I.Stage)
    (test : (input.experiment head).AdmissibleRule Local) :
    MeasurableSet (headCorrectGate input head test) :=
  measurableSet_eq_fun
    (test.measurable_decision.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    (measurable_fst.comp measurable_snd)

theorem selectedTestBranches_integral (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local)
    (goodCost : Good × (input.freshSuffix 1).World → ℝ≥0∞) (hgoodCost : Measurable goodCost)
    (badCost : Bad × (input.freshSuffix 1).World → ℝ≥0∞) (hbadCost : Measurable badCost) :
    (∫⁻ sample, if (pullbackTest (input.experiment head) test localSeed measurable_localSeed).rule.decision
        sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
        goodCost (goodSeed sample.1, referenceSuffixWorld input 1 sample.2)
      else badCost (badSeed sample.1, referenceSuffixWorld input 1 sample.2)
      ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw)) =
      (localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
          (∫⁻ child, goodCost child ∂goodLaw.prod (input.freshSuffix 1).worldLaw) +
        (localLaw.prod (input.stageLaw head)) (headCorrectGate input head test)ᶜ *
          (∫⁻ child, badCost child ∂badLaw.prod (input.freshSuffix 1).worldLaw) := by
  have h := selectedBranches_integral input head hhead localLaw goodLaw badLaw
      (headCorrectGate input head test) (measurableSet_headCorrectGate input head test)
      goodCost hgoodCost badCost hbadCost
  rw [← h]
  apply lintegral_congr
  intro sample
  have htape : worldTapes input sample.2 head = (sample.2 head).2 := by funext n; rfl
  simp only [pullbackTest, htape, headCorrectGate, Set.mem_ofPred_eq, StatisticalInput.truthAt]
  by_cases hc : test.rule.decision (localSeed sample.1) (sample.2 head).2 = (sample.2 head).1 <;>
    simp only [hc, ↓reduceIte]

end CombinedSelection

section ActualPolicy

variable {I : Instance} {Local Good Bad : Type*}
variable [MeasurableSpace Local] [MeasurableSpace Good] [MeasurableSpace Bad]

theorem localHeadSeed_law (input : StatisticalInput I) (head : I.Stage) (ν : Measure Local) :
    (input.seededWorldLaw ν).map (fun sample => (sample.1, sample.2 head)) =
      ν.prod (input.stageLaw head) := by
  have h := Measure.map_prod_map ν input.worldLaw measurable_id (measurable_pi_apply head)
  rw [Measure.map_id, input.worldLaw_coordinate] at h
  exact h.symm

theorem wrongMass_eq_bayesError (input : StatisticalInput I) (head : I.Stage)
    (ν : Measure Local) [IsProbabilityMeasure ν]
    (test : (input.experiment head).AdmissibleRule Local) :
    (ν.prod (input.stageLaw head)) (headCorrectGate input head test)ᶜ =
      (input.experiment head).bayesError ν test := by
  have hm := (measurableSet_headCorrectGate input head test).compl
  have hf : Measurable ((headCorrectGate input head test)ᶜ.indicator
      (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hm
  have hprojection : Measurable (fun sample : Local × input.World => (sample.1, sample.2 head)) :=
    measurable_fst.prodMk ((measurable_pi_apply head).comp measurable_snd)
  have h := lintegral_map (μ := input.seededWorldLaw ν)
    hf hprojection
  rw [localHeadSeed_law, lintegral_indicator_fun_one hm] at h
  rw [bayesError_eq_seededWorld_integral]
  exact h.trans (lintegral_congr (fun sample => by
    have htape : worldTapes input sample.2 head = (sample.2 head).2 := by funext n; rfl
    simp only [headCorrectGate, Set.indicator, Set.mem_compl_iff, Set.mem_ofPred_eq,
      htape, StatisticalInput.truthAt]))

theorem correctMass_add_bayesError (input : StatisticalInput I) (head : I.Stage)
    (ν : Measure Local) [IsProbabilityMeasure ν]
    (test : (input.experiment head).AdmissibleRule Local) :
    (ν.prod (input.stageLaw head)) (headCorrectGate input head test) +
      (input.experiment head).bayesError ν test = 1 := by
  rw [← wrongMass_eq_bayesError input head ν test]
  exact (measure_add_measure_compl (measurableSet_headCorrectGate input head test)).trans measure_univ

theorem runPenaltyCharge_pullbackAvailable {Large Small : Type*}
    [MeasurableSpace Large] [MeasurableSpace Small]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (policy : AvailablePolicy input C accounting available Small)
    (f : Large → Small) (hf : Measurable f) (penalty : ℝ≥0∞) (sample : Large × input.World) :
    runPenaltyCharge input C .uncapped accounting
      (pullbackAvailable input C accounting available policy f hf).val.rule penalty sample =
      runPenaltyCharge input C .uncapped accounting policy.val.rule penalty (f sample.1, sample.2) := by
  simp only [runPenaltyCharge, runObservationBill, run_pullbackAvailable, runSuccess_pullbackAvailable]

theorem selectedPolicyCharges_integral (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local)
    (goodAvailable badAvailable : Finset (I.freshSuffix 1).Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) goodAvailable Good)
    (bad : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) badAvailable Bad) (penalty : ℝ≥0∞) :
    (∫⁻ sample, if (pullbackTest (input.experiment head) test localSeed measurable_localSeed).rule.decision
        sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
        runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1))
          (pullbackAvailable (input.freshSuffix 1) _ _ goodAvailable good goodSeed measurable_goodSeed).val.rule
          penalty (sample.1, referenceSuffixWorld input 1 sample.2)
      else runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1))
        (pullbackAvailable (input.freshSuffix 1) _ _ badAvailable bad badSeed measurable_badSeed).val.rule
        penalty (sample.1, referenceSuffixWorld input 1 sample.2)
      ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw)) =
      (localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
        penaltyObjective (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule goodLaw penalty +
      (input.experiment head).bayesError localLaw test *
        penaltyObjective (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule badLaw penalty := by
  simp only [runPenaltyCharge_pullbackAvailable]
  rw [penaltyObjective_eq_lintegral_runPenaltyCharge _ _ _ _ _ good.val.measurable_rule,
    penaltyObjective_eq_lintegral_runPenaltyCharge _ _ _ _ _ bad.val.measurable_rule,
    ← wrongMass_eq_bayesError input head localLaw test]
  exact selectedTestBranches_integral input head hhead localLaw goodLaw badLaw test
    _ (measurable_runPenaltyCharge _ _ _ _ _ good.val.measurable_rule penalty)
    _ (measurable_runPenaltyCharge _ _ _ _ _ bad.val.measurable_rule penalty)

theorem headObservation_integral (input : StatisticalInput I) (head : I.Stage)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local) :
    (∫⁻ sample, (input.experiment head).observationCharge
      ((pullbackTest (input.experiment head) test localSeed measurable_localSeed).rule.stop sample.1
        (worldTapes input sample.2 head))
      ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw)) =
      (input.experiment head).bayesObservationCharge localLaw test := by
  rw [← bayesObservationCharge_eq_seededWorld_integral]
  simp only [BinaryExperiment.bayesObservationCharge, expectedObservationCharge_pullback, localSeed_law]

theorem selectedGoodOrPenalty_integral (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local)
    (goodAvailable : Finset (I.freshSuffix 1).Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) goodAvailable Good) (penalty : ℝ≥0∞) :
    (∫⁻ sample, if (pullbackTest (input.experiment head) test localSeed measurable_localSeed).rule.decision
        sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
        runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1))
          (pullbackAvailable (input.freshSuffix 1) _ _ goodAvailable good goodSeed measurable_goodSeed).val.rule
          penalty (sample.1, referenceSuffixWorld input 1 sample.2)
      else penalty ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw)) =
      (localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
        penaltyObjective (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule goodLaw penalty +
      (input.experiment head).bayesError localLaw test * penalty := by
  simp only [runPenaltyCharge_pullbackAvailable]
  rw [penaltyObjective_eq_lintegral_runPenaltyCharge _ _ _ _ _ good.val.measurable_rule,
    ← wrongMass_eq_bayesError input head localLaw test]
  have h := selectedTestBranches_integral input head hhead localLaw goodLaw badLaw test
    (runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule penalty)
    (measurable_runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule good.val.measurable_rule penalty)
    (fun _ => penalty) measurable_const
  simpa only [lintegral_const, measure_univ, mul_one, StatisticalInput.seededWorldLaw] using h

theorem someTool_objective_le (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (hdeferred : C.execution = .terminalBarrier) (accounting : NormalAccounting I)
    (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Good)
    (bad : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) (available.erase tool) Bad) (penalty : ℝ≥0∞) :
    let test' := pullbackTest (input.experiment head) test
      (localSeed (Good := Good) (Bad := Bad)) measurable_localSeed
    let good' := pullbackAvailable (input.freshSuffix 1) _ _ available good
      (goodSeed (Local := Local) (Bad := Bad)) measurable_goodSeed
    let bad' := pullbackAvailable (input.freshSuffix 1) _ _ (available.erase tool) bad
      (badSeed (Local := Local) (Good := Good)) measurable_badSeed
    penaltyObjective input C .uncapped accounting
      (bellmanHeadThenRule input head test' available
        (bellmanPostHeadRaw input head (some tool) good'.val.rule bad'.val.rule))
      (combinedLaw localLaw goodLaw badLaw) penalty ≤
      (input.experiment head).bayesObservationCharge localLaw test +
        ((localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
          penaltyObjective (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
            (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule goodLaw penalty +
        (input.experiment head).bayesError localLaw test *
          penaltyObjective (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
            (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule badLaw penalty) := by
  intro test' good' bad'
  let after := bellmanPostHeadRaw input head (some tool) good'.val.rule bad'.val.rule
  have hafter : MeasurableRule after :=
    measurable_bellmanPostHeadRaw input head (some tool) good'.val.rule bad'.val.rule
      good'.val.measurable_rule bad'.val.measurable_rule
  have hobs : Measurable (fun sample : CombinedSeed Local Good Bad × input.World =>
      (input.experiment head).observationCharge (test'.rule.stop sample.1 (worldTapes input sample.2 head))) :=
    (measurable_of_countable (input.experiment head).observationCharge).comp
      (test'.measurable_stop.comp
        (measurable_fst.prodMk (((measurable_pi_apply head).comp measurable_snd).snd)))
  rw [penaltyObjective_eq_lintegral_runPenaltyCharge _ _ _ _ _
    (measurable_bellmanHeadThenRule input head test' available after hafter)]
  calc
    _ ≤ ∫⁻ sample, (input.experiment head).observationCharge
          (test'.rule.stop sample.1 (worldTapes input sample.2 head)) +
        (if test'.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
          runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
            (zeroNormalAccounting (I.freshSuffix 1)) good'.val.rule penalty
            (sample.1, referenceSuffixWorld input 1 sample.2)
        else runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) bad'.val.rule penalty
          (sample.1, referenceSuffixWorld input 1 sample.2))
        ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw) := by
      apply lintegral_mono
      intro sample
      exact bellmanHeadThen_someTool_penaltyCharge_le input C hearly hcurrent hdeferred accounting
        head hhead test' available tool htool heligible good' bad' sample penalty
    _ = _ := by
      rw [lintegral_add_left hobs, headObservation_integral input head localLaw goodLaw badLaw test]
      congr 1
      exact selectedPolicyCharges_integral input head hhead localLaw goodLaw badLaw test
        available (available.erase tool) good bad penalty

theorem noTool_objective_le (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (hdeferred : C.execution = .terminalBarrier) (accounting : NormalAccounting I)
    (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local) (available : Finset I.Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Good)
    (bad : PolicyRule (I.freshSuffix 1) (CombinedSeed Local Good Bad))
    (hbad : MeasurableRule bad) (penalty : ℝ≥0∞) :
    let test' := pullbackTest (input.experiment head) test
      (localSeed (Good := Good) (Bad := Bad)) measurable_localSeed
    let good' := pullbackAvailable (input.freshSuffix 1) _ _ available good
      (goodSeed (Local := Local) (Bad := Bad)) measurable_goodSeed
    penaltyObjective input C .uncapped accounting
      (bellmanHeadThenRule input head test' available
        (bellmanPostHeadRaw input head none good'.val.rule bad))
      (combinedLaw localLaw goodLaw badLaw) penalty ≤
      (input.experiment head).bayesObservationCharge localLaw test +
        ((localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
          penaltyObjective (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
            (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule goodLaw penalty +
        (input.experiment head).bayesError localLaw test * penalty) := by
  intro test' good'
  let after := bellmanPostHeadRaw input head none good'.val.rule bad
  have hafter : MeasurableRule after :=
    measurable_bellmanPostHeadRaw input head none good'.val.rule bad good'.val.measurable_rule hbad
  have hobs : Measurable (fun sample : CombinedSeed Local Good Bad × input.World =>
      (input.experiment head).observationCharge (test'.rule.stop sample.1 (worldTapes input sample.2 head))) :=
    (measurable_of_countable (input.experiment head).observationCharge).comp
      (test'.measurable_stop.comp
        (measurable_fst.prodMk (((measurable_pi_apply head).comp measurable_snd).snd)))
  rw [penaltyObjective_eq_lintegral_runPenaltyCharge _ _ _ _ _
    (measurable_bellmanHeadThenRule input head test' available after hafter)]
  calc
    _ ≤ ∫⁻ sample, (input.experiment head).observationCharge
          (test'.rule.stop sample.1 (worldTapes input sample.2 head)) +
        (if test'.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
          runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
            (zeroNormalAccounting (I.freshSuffix 1)) good'.val.rule penalty
            (sample.1, referenceSuffixWorld input 1 sample.2)
        else penalty) ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw) := by
      apply lintegral_mono
      intro sample
      exact bellmanHeadThen_noTool_penaltyCharge_le input C hearly hcurrent hdeferred accounting
        head hhead test' available good' bad hbad sample penalty
    _ = _ := by
      rw [lintegral_add_left hobs, headObservation_integral input head localLaw goodLaw badLaw test]
      congr 1
      exact selectedGoodOrPenalty_integral input head hhead localLaw goodLaw badLaw test available good penalty

end ActualPolicy

end PaperProofs.Common.Native.BellmanExpectation
