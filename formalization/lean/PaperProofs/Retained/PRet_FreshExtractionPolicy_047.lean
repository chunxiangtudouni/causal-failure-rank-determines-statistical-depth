module

public import PaperProofs.Retained.PRet_EntryReplay_045
public import PaperProofs.Retained.PRet_DelayedPolicy_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshExtractionPolicy047

open Common Common.Native MeasureTheory PRetInformationPackets006 PRetDelayedPolicy010 PRetEntryReplay045

variable {I : Instance}

/-- The fresh comparison follows source information only. Original source
allocations/executions are public administrative shadow steps; they are not
fresh paid actions and old H is retained by the fresh success predicate. -/
def candidate (first : ℕ) (source : Startup I) (sourceAction : Action I)
    (history : List (VisibleEvent (I.freshSuffix first))) : Action (I.freshSuffix first) :=
  if source.halted then
    if source.abandoned then .abandon else
      if source.finished then catchUp history (I.freshSuffix first).stageCount .stop else .stop
  else match sourceAction with
    | .review stage => if hfuture : first ≤ stage.val then
        let target := suffixStageOf first stage hfuture
        catchUp history target.val (.review target)
      else .abandon
    | .write stage bit => if hfuture : first ≤ stage.val then
        let target := suffixStageOf first stage hfuture
        catchUp history target.val (.write target bit)
      else .abandon
    | _ => .abandon

noncomputable def raw {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (startup : Startup I) : PolicyRule (I.freshSuffix first) Seed :=
  fun seed history =>
    match shadowFrom first accounting source startup seed history with
    | none => .abandon
    | some cached => candidate first cached (source seed cached.history) history

noncomputable def rule {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (startup : Startup I) : PolicyRule (I.freshSuffix first) Seed :=
  PRetRetainedGuard007.guarded (raw first accounting source startup)

theorem measurable_raw {Seed : Type*} [MeasurableSpace Seed] (first : ℕ) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hsource : MeasurableRule source) (startup : Startup I) :
    MeasurableRule (raw first accounting source startup) := by
  change Measurable (fun sample : Seed × List (VisibleEvent (I.freshSuffix first)) =>
    raw first accounting source startup sample.1 sample.2)
  let defaultSource := publicStartup (initial (I := I) (fun _ => false))
  let selected := fun sample : Seed × List (VisibleEvent (I.freshSuffix first)) =>
    shadowFrom first accounting source startup sample.1 sample.2
  have hs : Measurable selected := measurable_shadowFrom first accounting source hsource startup
  have hd : Measurable (fun sample : Seed × List (VisibleEvent (I.freshSuffix first)) =>
      (selected sample).getD defaultSource) :=
    (measurable_of_countable (fun cached : Option (Startup I) => cached.getD defaultSource)).comp hs
  have hh : Measurable (fun sample : Seed × List (VisibleEvent (I.freshSuffix first)) =>
      ((selected sample).getD defaultSource).history) :=
    (measurable_of_countable (fun cached : Startup I => cached.history)).comp hd
  have ha := hsource.comp (measurable_fst.prodMk hh)
  have hm : Measurable (fun data : Option (Startup I) × Action I × List (VisibleEvent (I.freshSuffix first)) =>
      match data.1 with
      | none => (Action.abandon : Action (I.freshSuffix first))
      | some cached => candidate first cached data.2.1 data.2.2) := measurable_of_countable _
  convert hm.comp (hs.prodMk (ha.prodMk measurable_snd)) using 1
  funext sample
  cases h : shadowFrom first accounting source startup sample.1 sample.2 with
  | none => simp [raw, selected, h]
  | some cached => simp [raw, selected, h]

theorem measurable_rule {Seed : Type*} [MeasurableSpace Seed] (first : ℕ) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hsource : MeasurableRule source) (startup : Startup I) :
    MeasurableRule (rule first accounting source startup) :=
  PRetRetainedGuard007.measurable_guarded (raw first accounting source startup)
    (measurable_raw first accounting source hsource startup)

/-- A REAL globally admissible full fresh Policy, even for malformed initial
snapshots or arbitrary private seeds. Performance is established later only
on genuine source-entry snapshots; it is not inserted in this Policy type. -/
noncomputable def policy {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I)
    (first : ℕ) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hsource : MeasurableRule source) (startup : Startup I) :
    Policy (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) Seed where
  rule := rule first accounting source startup
  measurable_rule := measurable_rule first accounting source hsource startup
  legal := PRetRetainedGuard007.guarded_legal (input.freshSuffix first) (freshContract (I.freshSuffix first))
    ⟨rfl, rfl, rfl⟩ (zeroNormalAccounting (I.freshSuffix first)) (raw first accounting source startup)

theorem raw_of_shadow {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (startup cached : Startup I) (seed : Seed)
    (history : List (VisibleEvent (I.freshSuffix first)))
    (hs : shadowFrom first accounting source startup seed history = some cached) :
    raw first accounting source startup seed history = candidate first cached (source seed cached.history) history := by
  rw [raw, hs]

end PaperProofs.Retained.PRetFreshExtractionPolicy047
