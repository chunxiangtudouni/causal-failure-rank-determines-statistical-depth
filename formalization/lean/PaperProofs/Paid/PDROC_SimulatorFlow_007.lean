module

public import PaperProofs.Paid.PDROC_SimulatorFlow_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

/-- Lift of the next-entry projection to the original optional stage-exit
kernel. Missing prior entry and missing exit are both preserved as none. -/
def simulatorNextEntryOptionalProjection (next : I.Stage)
    (result : (Seed × EntryHistory I) × EntryHistory I) : Seed × EntryHistory I :=
  (result.1.1, result.2.bind (fun exit =>
    if result.1.2.isSome = true ∧ historyHalted exit = false ∧ historyCursor exit = next.val
    then some exit else none))

theorem measurable_simulatorNextEntryOptionalProjection [MeasurableSpace Seed] (next : I.Stage) :
    Measurable (simulatorNextEntryOptionalProjection (Seed := Seed) next) := by
  have hm : Measurable (fun pair : EntryHistory I × EntryHistory I => pair.2.bind (fun exit =>
      if pair.1.isSome = true ∧ historyHalted exit = false ∧ historyCursor exit = next.val
      then some exit else none)) := measurable_of_countable _
  exact (measurable_fst.comp measurable_fst).prodMk
    (hm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem simulatorNextEntryOptionalProjection_some (next : I.Stage) (seed : Seed)
    (prior : EntryHistory I) (exit : List (VisibleEvent I)) :
    simulatorNextEntryOptionalProjection next ((seed, prior), some exit) =
      simulatorNextEntryProjection next ((seed, prior), exit) := by
  rfl

theorem simulatorNextEntryOptionalProjection_no_exit (next : I.Stage) (seed : Seed) (prior : EntryHistory I) :
    simulatorNextEntryOptionalProjection next ((seed, prior), none) = (seed, none) := by
  rfl

theorem simulatorNextEntryOptionalProjection_no_prior (next : I.Stage) (seed : Seed) (exit : EntryHistory I) :
    simulatorNextEntryOptionalProjection next ((seed, none), exit) = (seed, none) := by
  cases exit with
  | none => rfl
  | some history =>
    exact (simulatorNextEntryOptionalProjection_some next seed none history).trans
      (simulatorNextEntryProjection_prior_none next seed history)

theorem simulatorNextEntryOptionalProjection_fst (next : I.Stage)
    (result : (Seed × EntryHistory I) × EntryHistory I) :
    (simulatorNextEntryOptionalProjection next result).1 = result.1.1 := by
  rfl

variable [MeasurableSpace Seed]

theorem sourceEventualStageExitSome_nextEntry_of_finite (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (stage next : P.sharedInstance.Stage) (hnext : next.val = stage.val + 1)
    (sample : Seed × (P.input fee hfee).World)
    (hs : (simulatorLocalTest P fee hfee (sourceForOptionalHistory source.rule)
      (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage).rule.stop
        (sourceEventualStageSample P fee hfee C accounting source stage sample).1
        (sourceEventualStageSample P fee hfee C accounting source stage sample).2.2 ≠ ⊤) :
    entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule next sample =
      simulatorNextEntryOptionalProjection next (sourceEventualStageExitSome P fee hfee C accounting source stage sample) := by
  exact sourceEventualReportedDraw_nextEntry_of_finite P fee hfee C accounting source stage next hnext sample hs

end PDROC
