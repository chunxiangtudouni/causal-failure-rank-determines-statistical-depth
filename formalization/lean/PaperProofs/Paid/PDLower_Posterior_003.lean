module

public import PaperProofs.Paid.PDLower_Information_001
public import PaperProofs.Paid.PDLower_Survival_002
public import PaperProofs.Paid.PDROC_DirectEntry_003
public import PaperProofs.Paid.PDROC_StageObservables_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

local instance posteriorOptionBoolMeasurable : MeasurableSpace (Option Bool) := ⊤
local instance posteriorOptionBoolSingleton : MeasurableSingletonClass (Option Bool) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

noncomputable def pastEntryRecord (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage)
    (past : Seed × (P.input fee hf).PastWorld stage) : Seed × EntryHistory P.sharedInstance :=
  (past.1, entryHistory (P.input fee hf) C.val .uncapped accounting source.rule stage
    (past.1, completePastWorld (P.input fee hf) stage past.2))

theorem measurable_pastEntryRecord (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage) :
    Measurable (pastEntryRecord P fee hf C accounting source stage) :=
  measurable_fst.prodMk ((measurable_entryHistory (P.input fee hf) C.val .uncapped accounting
    source.rule source.measurable_rule stage).comp
      (measurable_fst.prodMk ((measurable_completePastWorld (P.input fee hf) stage).comp measurable_snd)))

theorem pastEntryRecord_preBirth (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage)
    (sample : Seed × (P.input fee hf).World) :
    pastEntryRecord P fee hf C accounting source stage ((P.input fee hf).preBirthView stage sample) =
      entryHistorySeedRecord (P.input fee hf) C.val .uncapped accounting source.rule stage sample := by
  refine Prod.ext rfl ?_
  exact entryHistory_eq_of_past (P.input fee hf) C.val .uncapped accounting source.rule source.legal
    sample.1 sample.2 (completePastWorld (P.input fee hf) stage (fun i => sample.2 i.val)) stage
      (fun i hi => completePastWorld_apply_past (P.input fee hf) stage (fun i => sample.2 i.val) i hi)

noncomputable def pastEntryTest (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage) :
    P.binarySymmetric.experiment.AdmissibleRule (Seed × (P.input fee hf).PastWorld stage) :=
  PDROC.pullbackSeedTest P.binarySymmetric.experiment
    (PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage)
    (pastEntryRecord P fee hf C accounting source stage)
    (measurable_pastEntryRecord P fee hf C accounting source stage)

theorem pastEntryTest_stop_eq_count (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage)
    (sample : Seed × (P.input fee hf).World) :
    (pastEntryTest P fee hf C accounting source stage).rule.stop
      ((P.input fee hf).preBirthView stage sample) (sample.2 stage).2 =
      P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage := by
  change (PDROC.sourceEventualEntryTest P fee hf source.rule source.measurable_rule stage).rule.stop
    (pastEntryRecord P fee hf C accounting source stage ((P.input fee hf).preBirthView stage sample)) _ = _
  rw [pastEntryRecord_preBirth]
  exact eventualTest_stop_eq_count P fee hf C accounting source sample stage

def recordReviewHistory (P : Parameters) (stage : P.sharedInstance.Stage)
    (word : P.binarySymmetric.experiment.StoppedWord) : List (VisibleEvent P.sharedInstance) :=
  List.ofFn (fun k : Fin word.1 => .observation stage (word.2 k).val)

/-- Record decoder for the original ordinary bit, or MAP if the first
nonreview action leaves the bit unmade. It never reads current truth. -/
noncomputable def completedRecordDecision (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage)
    (record : (Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.StoppedWord) : Bool :=
  let entry := (pastEntryRecord P fee hf C accounting source stage record.1).2
  let mapBit := P.experiment.posteriorRecordDecision ((), record.2)
  if entry.isSome = true then
    (PDROC.optionWriteBit (source.rule record.1.1 (entry.getD [] ++ recordReviewHistory P stage record.2))).getD mapBit
  else mapBit

theorem measurable_completedRecordDecision (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hf) C.val .uncapped accounting Seed) (stage : P.sharedInstance.Stage) :
    Measurable (completedRecordDecision P fee hf C accounting source stage) := by
  have hentry : Measurable (fun record : (Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.StoppedWord =>
      (pastEntryRecord P fee hf C accounting source stage record.1).2) :=
    ((measurable_pastEntryRecord P fee hf C accounting source stage).comp measurable_fst).snd
  have hhist : Measurable (fun record : (Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.StoppedWord =>
      ((pastEntryRecord P fee hf C accounting source stage record.1).2).getD [] ++ recordReviewHistory P stage record.2) :=
    (measurable_of_countable (fun pair : EntryHistory P.sharedInstance × P.binarySymmetric.experiment.StoppedWord =>
      pair.1.getD [] ++ recordReviewHistory P stage pair.2)).comp (hentry.prodMk measurable_snd)
  have ha := source.measurable_rule.comp (measurable_fst.fst.prodMk hhist)
  have hbit := (measurable_of_countable (fun action : Action P.sharedInstance => PDROC.optionWriteBit action)).comp ha
  have hmap : Measurable (fun record : (Seed × (P.input fee hf).PastWorld stage) × P.binarySymmetric.experiment.StoppedWord =>
      P.experiment.posteriorRecordDecision ((), record.2)) :=
    (measurable_of_countable (fun word : P.binarySymmetric.experiment.StoppedWord =>
      P.experiment.posteriorRecordDecision ((), word))).comp measurable_snd
  have hchoose : Measurable (fun pair : Option Bool × Bool => pair.1.getD pair.2) := measurable_of_countable _
  exact (hchoose.comp (hbit.prodMk hmap)).ite
    (((measurable_of_countable (fun entry : EntryHistory P.sharedInstance => entry.isSome)).comp hentry)
      (measurableSet_singleton true)) hmap

end PDLower
