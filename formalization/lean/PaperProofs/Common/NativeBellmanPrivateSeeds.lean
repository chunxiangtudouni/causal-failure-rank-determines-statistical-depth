module

public import PaperProofs.Common.NativeBellmanUpper

/-!
Private-seed assembly for the actual B08 epsilon construction. The local
test, good continuation and bad continuation keep their original seed laws
as the three projections of a product seed. Pullback preserves their exact
original objectives, including infinite bills; no optimizer is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.BellmanPrivateSeeds

open PaperProofs.Statistics

section PullbackTest

variable {Large Small : Type*} [MeasurableSpace Large] [MeasurableSpace Small]

def pullbackTest (E : BinaryExperiment) (test : E.AdmissibleRule Small)
    (f : Large → Small) (hf : Measurable f) : E.AdmissibleRule Large where
  rule := {
    stop := fun seed tape => test.rule.stop (f seed) tape
    decision := fun seed tape => test.rule.decision (f seed) tape
    stopping := fun seed => test.rule.stopping (f seed)
    stoppedDecision := fun seed => test.rule.stoppedDecision (f seed)
  }
  measurable_stop := test.measurable_stop.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  measurable_decision := test.measurable_decision.comp ((hf.comp measurable_fst).prodMk measurable_snd)

theorem conditionalLaw_map_seed (E : BinaryExperiment) (ν : Measure Large)
    (f : Large → Small) (hf : Measurable f) (truth : Bool) :
    E.conditionalLaw (ν.map f) truth =
      (E.conditionalLaw ν truth).map (fun sample => (f sample.1, sample.2)) := by
  have h := Measure.map_prod_map ν (E.tapeLaw truth) hf measurable_id
  rw [Measure.map_id] at h
  change (ν.map f).prod (E.tapeLaw truth) =
    (ν.prod (E.tapeLaw truth)).map (fun sample => (f sample.1, sample.2)) at h
  exact h

theorem expectedObservationCharge_pullback (E : BinaryExperiment)
    (test : E.AdmissibleRule Small) (f : Large → Small) (hf : Measurable f)
    (ν : Measure Large) (truth : Bool) :
    E.expectedObservationCharge ν (pullbackTest E test f hf) truth =
      E.expectedObservationCharge (ν.map f) test truth := by
  symm
  unfold BinaryExperiment.expectedObservationCharge
  have hm : Measurable (fun sample : Large × E.Tape => (f sample.1, sample.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  have hc : Measurable (fun sample : Small × E.Tape =>
      E.observationCharge (test.rule.stop sample.1 sample.2)) :=
    (measurable_of_countable E.observationCharge).comp test.measurable_stop
  rw [conditionalLaw_map_seed E ν f hf truth,
    lintegral_map hc hm]
  rfl

theorem conditionalError_pullback (E : BinaryExperiment)
    (test : E.AdmissibleRule Small) (f : Large → Small) (hf : Measurable f)
    (ν : Measure Large) (truth : Bool) :
    E.conditionalError ν (pullbackTest E test f hf) truth =
      E.conditionalError (ν.map f) test truth := by
  symm
  unfold BinaryExperiment.conditionalError
  have hs : MeasurableSet {sample : Small × E.Tape | test.rule.decision sample.1 sample.2 ≠ truth} :=
    ((measurableSet_singleton truth).preimage test.measurable_decision).compl
  have hm : Measurable (fun sample : Large × E.Tape => (f sample.1, sample.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  rw [conditionalLaw_map_seed E ν f hf truth,
    Measure.map_apply hm hs]
  rfl

theorem bayesObjective_pullback (E : BinaryExperiment)
    (test : E.AdmissibleRule Small) (f : Large → Small) (hf : Measurable f)
    (ν : Measure Large) (penalty : ℝ≥0∞) :
    E.bayesObjective ν (pullbackTest E test f hf) penalty =
      E.bayesObjective (ν.map f) test penalty := by
  simp only [BinaryExperiment.bayesObjective, BinaryExperiment.bayesObservationCharge,
    BinaryExperiment.bayesError, expectedObservationCharge_pullback, conditionalError_pullback]

end PullbackTest

section PullbackPolicy

variable {I : Instance} {Large Small : Type*} [MeasurableSpace Large] [MeasurableSpace Small]

def pullbackAvailable (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Small)
    (f : Large → Small) (hf : Measurable f) : AvailablePolicy input C accounting available Large := by
  refine ⟨{
    rule := fun seed history => policy.val.rule (f seed) history
    measurable_rule := policy.val.measurable_rule.comp ((hf.comp measurable_fst).prodMk measurable_snd)
    legal := ?_ }, ?_⟩
  · intro seed truth tapes n s hp ha
    have hp' := prefix_rule_transport input C .uncapped accounting
      (fun seed history => policy.val.rule (f seed) history) policy.val.rule seed (f seed)
      (fun _ => rfl) truth tapes hp
    exact policy.val.legal (f seed) truth tapes n s hp' ha
  · intro seed truth tapes n s hp ha handle tool heq
    have hp' := prefix_rule_transport input C .uncapped accounting
      (fun seed history => policy.val.rule (f seed) history) policy.val.rule seed (f seed)
      (fun _ => rfl) truth tapes hp
    exact policy.property (f seed) truth tapes n s hp' ha handle tool heq

theorem run_pullbackAvailable (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Small)
    (f : Large → Small) (hf : Measurable f) (sample : Large × input.World) (n : ℕ) :
    run input C .uncapped accounting (pullbackAvailable input C accounting available policy f hf).val.rule sample n =
      run input C .uncapped accounting policy.val.rule (f sample.1, sample.2) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih]; rfl

theorem runSuccess_pullbackAvailable (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Small)
    (f : Large → Small) (hf : Measurable f) (sample : Large × input.World) :
    runSuccess input C .uncapped accounting (pullbackAvailable input C accounting available policy f hf).val.rule sample ↔
      runSuccess input C .uncapped accounting policy.val.rule (f sample.1, sample.2) := by
  simp only [runSuccess, run_pullbackAvailable]

theorem expectedObservationBill_pullbackAvailable (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Small)
    (f : Large → Small) (hf : Measurable f) (ν : Measure Large) :
    expectedObservationBill input C .uncapped accounting
      (pullbackAvailable input C accounting available policy f hf).val.rule ν =
        expectedObservationBill input C .uncapped accounting policy.val.rule (ν.map f) := by
  symm
  unfold expectedObservationBill
  have hm : Measurable (fun sample : Large × input.World => (f sample.1, sample.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  rw [seededWorldLaw_map_seed input ν f hf,
    lintegral_map (measurable_runObservationBill input C .uncapped accounting policy.val.rule policy.val.measurable_rule)
      hm]
  apply lintegral_congr
  intro sample
  simp only [runObservationBill, run_pullbackAvailable]

theorem risk_pullbackAvailable (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Small)
    (f : Large → Small) (hf : Measurable f) (ν : Measure Large) :
    risk input C .uncapped accounting (pullbackAvailable input C accounting available policy f hf).val.rule ν =
      risk input C .uncapped accounting policy.val.rule (ν.map f) := by
  symm
  unfold risk
  have hs : MeasurableSet {sample : Small × input.World | ¬runSuccess input C .uncapped accounting policy.val.rule sample} :=
    (measurableSet_runSuccess input C .uncapped accounting policy.val.rule policy.val.measurable_rule).compl
  have hm : Measurable (fun sample : Large × input.World => (f sample.1, sample.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  rw [seededWorldLaw_map_seed input ν f hf,
    Measure.map_apply hm hs]
  congr 1
  ext sample
  exact (not_congr (runSuccess_pullbackAvailable input C accounting available policy f hf sample)).symm

theorem penaltyObjective_pullbackAvailable (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Small)
    (f : Large → Small) (hf : Measurable f) (ν : Measure Large) (penalty : ℝ≥0∞) :
    penaltyObjective input C .uncapped accounting
      (pullbackAvailable input C accounting available policy f hf).val.rule ν penalty =
        penaltyObjective input C .uncapped accounting policy.val.rule (ν.map f) penalty := by
  rw [penaltyObjective, penaltyObjective,
    expectedObservationBill_pullbackAvailable, risk_pullbackAvailable]

end PullbackPolicy

section TripleSeed

variable {Local Good Bad : Type*}
variable [MeasurableSpace Local] [MeasurableSpace Good] [MeasurableSpace Bad]

abbrev CombinedSeed (Local Good Bad : Type*) := Local × (Good × Bad)

noncomputable def combinedLaw (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad) :
    Measure (CombinedSeed Local Good Bad) := localLaw.prod (goodLaw.prod badLaw)

def localSeed : CombinedSeed Local Good Bad → Local := Prod.fst
def goodSeed : CombinedSeed Local Good Bad → Good := fun seed => seed.2.1
def badSeed : CombinedSeed Local Good Bad → Bad := fun seed => seed.2.2

theorem measurable_localSeed : Measurable (localSeed (Local := Local) (Good := Good) (Bad := Bad)) := measurable_fst
theorem measurable_goodSeed : Measurable (goodSeed (Local := Local) (Good := Good) (Bad := Bad)) := measurable_fst.comp measurable_snd
theorem measurable_badSeed : Measurable (badSeed (Local := Local) (Good := Good) (Bad := Bad)) := measurable_snd.comp measurable_snd

variable (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
variable [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]

instance combinedLaw_probability : IsProbabilityMeasure (combinedLaw localLaw goodLaw badLaw) := by
  unfold combinedLaw
  infer_instance

omit [IsProbabilityMeasure localLaw] in
theorem localSeed_law : (combinedLaw localLaw goodLaw badLaw).map localSeed = localLaw := by
  simp only [combinedLaw, localSeed, Measure.map_fst_prod, measure_univ, one_smul]

theorem goodSeed_law : (combinedLaw localLaw goodLaw badLaw).map goodSeed = goodLaw := by
  change (localLaw.prod (goodLaw.prod badLaw)).map (Prod.fst ∘ Prod.snd) = goodLaw
  rw [← Measure.map_map measurable_fst measurable_snd]
  simp only [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_fst_prod]

theorem badSeed_law : (combinedLaw localLaw goodLaw badLaw).map badSeed = badLaw := by
  change (localLaw.prod (goodLaw.prod badLaw)).map (Prod.snd ∘ Prod.snd) = badLaw
  rw [← Measure.map_map measurable_snd measurable_snd]
  simp only [Measure.map_snd_prod, measure_univ, one_smul]

omit [IsProbabilityMeasure localLaw] in
theorem localGood_jointLaw :
    (combinedLaw localLaw goodLaw badLaw).map (fun seed => (localSeed seed, goodSeed seed)) =
      localLaw.prod goodLaw := by
  have h := Measure.map_prod_map localLaw (goodLaw.prod badLaw) measurable_id measurable_fst
  rw [Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul] at h
  change localLaw.prod goodLaw =
    (combinedLaw localLaw goodLaw badLaw).map (fun seed => (localSeed seed, goodSeed seed)) at h
  exact h.symm

omit [IsProbabilityMeasure localLaw] in
theorem localBad_jointLaw :
    (combinedLaw localLaw goodLaw badLaw).map (fun seed => (localSeed seed, badSeed seed)) =
      localLaw.prod badLaw := by
  have h := Measure.map_prod_map localLaw (goodLaw.prod badLaw) measurable_id measurable_snd
  rw [Measure.map_id, Measure.map_snd_prod, measure_univ, one_smul] at h
  change localLaw.prod badLaw =
    (combinedLaw localLaw goodLaw badLaw).map (fun seed => (localSeed seed, badSeed seed)) at h
  exact h.symm

theorem goodBad_jointLaw :
    (combinedLaw localLaw goodLaw badLaw).map (fun seed => (goodSeed seed, badSeed seed)) =
      goodLaw.prod badLaw := by
  change (localLaw.prod (goodLaw.prod badLaw)).map Prod.snd = goodLaw.prod badLaw
  simp only [Measure.map_snd_prod, measure_univ, one_smul]

omit [IsProbabilityMeasure localLaw] in
theorem localObjective_combinedLaw (E : BinaryExperiment) (test : E.AdmissibleRule Local)
    (penalty : ℝ≥0∞) :
    E.bayesObjective (combinedLaw localLaw goodLaw badLaw)
      (pullbackTest E test localSeed measurable_localSeed) penalty =
        E.bayesObjective localLaw test penalty := by
  rw [bayesObjective_pullback, localSeed_law]

theorem goodPenaltyObjective_combinedLaw {I : Instance} (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Good) (penalty : ℝ≥0∞) :
    penaltyObjective input C .uncapped accounting
      (pullbackAvailable input C accounting available policy goodSeed measurable_goodSeed).val.rule
      (combinedLaw localLaw goodLaw badLaw) penalty =
        penaltyObjective input C .uncapped accounting policy.val.rule goodLaw penalty := by
  rw [penaltyObjective_pullbackAvailable, goodSeed_law]

theorem badPenaltyObjective_combinedLaw {I : Instance} (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : AvailablePolicy input C accounting available Bad) (penalty : ℝ≥0∞) :
    penaltyObjective input C .uncapped accounting
      (pullbackAvailable input C accounting available policy badSeed measurable_badSeed).val.rule
      (combinedLaw localLaw goodLaw badLaw) penalty =
        penaltyObjective input C .uncapped accounting policy.val.rule badLaw penalty := by
  rw [penaltyObjective_pullbackAvailable, badSeed_law]

end TripleSeed

end PaperProofs.Common.Native.BellmanPrivateSeeds
