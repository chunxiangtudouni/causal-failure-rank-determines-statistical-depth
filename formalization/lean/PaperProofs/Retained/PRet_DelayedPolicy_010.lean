module

public import PaperProofs.Retained.PRet_InformationPackets_006
public import PaperProofs.Retained.PRet_RetainedGuard_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetDelayedPolicy010

open Common Common.Native MeasureTheory PRetInformationPackets006

variable {I : Instance}

def catchUp (history : List (VisibleEvent I)) (destination : ℕ) (next : Action I) : Action I :=
  if historyCursor history < destination then
    if hstage : historyCursor history < I.stageCount then .advance ⟨historyCursor history, hstage⟩ else .abandon
  else if historyCursor history = destination then next else .abandon

/-- At the barrier pay exactly the actual source executions, in source
order. Handles are rebound to the target's actual ordinary write serials.
No pending-but-unexecuted source commitment is charged. -/
def paymentAction (source : Startup I) (history : List (VisibleEvent I)) : Action I :=
  match source.executions[(historyExecutions history).length]? with
  | none => .stop
  | some execution =>
    let handle : MismatchHandle I := ⟨execution.handle.stage, historyWriteSerial history execution.handle.stage⟩
    match (historyCommitments history).find? (fun pair => pair.1.stage == execution.handle.stage) with
    | none => .allocate handle execution.tool
    | some pair => if pair.2 = execution.tool then .execute handle execution.tool else .abandon

def candidate (source : Startup I) (sourceAction : Action I) (history : List (VisibleEvent I)) : Action I :=
  if source.halted then
    if source.abandoned then .abandon else
      if source.finished then catchUp history I.stageCount (paymentAction source history) else .stop
  else match sourceAction with
    | .review stage => catchUp history stage.val (.review stage)
    | .write stage bit => catchUp history stage.val (.write stage bit)
    | _ => .abandon

noncomputable def raw {Seed : Type*} (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed) :
    PolicyRule I Seed := fun seed history =>
  match shadow accounting sourceRule seed history with
  | none => .abandon
  | some source => candidate source (sourceRule seed source.history) history

noncomputable def rule {Seed : Type*} (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed) :
    PolicyRule I Seed := PRetRetainedGuard007.guarded (raw accounting sourceRule)

theorem measurable_raw {Seed : Type*} [MeasurableSpace Seed] (accounting : NormalAccounting I)
    (sourceRule : PolicyRule I Seed) (hsource : MeasurableRule sourceRule) :
    MeasurableRule (raw accounting sourceRule) := by
  change Measurable (fun sample : Seed × List (VisibleEvent I) => raw accounting sourceRule sample.1 sample.2)
  let defaultSource := publicStartup (initial (I := I) (fun _ => false))
  let selected : Seed × List (VisibleEvent I) → Option (Startup I) := fun sample =>
    shadow accounting sourceRule sample.1 sample.2
  have hs : Measurable selected := measurable_shadow accounting sourceRule hsource
  have hd : Measurable (fun sample : Seed × List (VisibleEvent I) => (selected sample).getD defaultSource) :=
    (measurable_of_countable (fun source : Option (Startup I) => source.getD defaultSource)).comp hs
  have hh : Measurable (fun sample : Seed × List (VisibleEvent I) =>
      ((selected sample).getD defaultSource).history) :=
    (measurable_of_countable (fun source : Startup I => source.history)).comp hd
  have ha := hsource.comp (measurable_fst.prodMk hh)
  have hm : Measurable (fun input : Option (Startup I) × Action I × List (VisibleEvent I) =>
      match input.1 with
      | none => Action.abandon
      | some source => candidate source input.2.1 input.2.2) := measurable_of_countable _
  convert hm.comp (hs.prodMk (ha.prodMk measurable_snd)) using 1
  funext sample
  cases h : shadow accounting sourceRule sample.1 sample.2 with
  | none => simp [raw, selected, h]
  | some source => simp [raw, selected, h]

theorem measurable_rule {Seed : Type*} [MeasurableSpace Seed] (accounting : NormalAccounting I)
    (sourceRule : PolicyRule I Seed) (hsource : MeasurableRule sourceRule) :
    MeasurableRule (rule accounting sourceRule) :=
  PRetRetainedGuard007.measurable_guarded (raw accounting sourceRule) (measurable_raw accounting sourceRule hsource)

noncomputable def policy {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed) (hsource : MeasurableRule sourceRule) :
    Policy input C .uncapped accounting Seed where
  rule := rule accounting sourceRule
  measurable_rule := measurable_rule accounting sourceRule hsource
  legal := PRetRetainedGuard007.guarded_legal input C hretained accounting (raw accounting sourceRule)

def isCorrection : Action I → Bool
  | .allocate _ _ | .execute _ _ => true
  | _ => false

theorem catchUp_correction (history : List (VisibleEvent I)) (destination : ℕ) (next : Action I)
    (hcorrection : isCorrection (catchUp history destination next) = true) :
    historyCursor history = destination ∧ isCorrection next = true := by
  unfold catchUp at hcorrection
  split_ifs at hcorrection with hbefore hstage hsame
  · cases hcorrection
  · cases hcorrection
  · exact ⟨hsame, hcorrection⟩
  · cases hcorrection

theorem candidate_correction (source : Startup I) (sourceAction : Action I) (history : List (VisibleEvent I))
    (hcorrection : isCorrection (candidate source sourceAction history) = true) :
    historyCursor history = I.stageCount := by
  unfold candidate at hcorrection
  split_ifs at hcorrection
  · cases hcorrection
  · exact (catchUp_correction history I.stageCount _ hcorrection).1
  · cases hcorrection
  · cases sourceAction
    all_goals first
      | exact False.elim (Bool.false_ne_true ((catchUp_correction history _ _ hcorrection).2))
      | cases hcorrection

theorem rule_correction {Seed : Type*} (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed)
    (seed : Seed) (history : List (VisibleEvent I))
    (hcorrection : isCorrection (rule accounting sourceRule seed history) = true) :
    historyCursor history = I.stageCount := by
  unfold rule PRetRetainedGuard007.guarded at hcorrection
  split_ifs at hcorrection
  · unfold raw at hcorrection
    cases hs : shadow accounting sourceRule seed history with
    | none => simp only [hs, isCorrection, Bool.false_eq_true] at hcorrection
    | some source => exact candidate_correction source _ history (by simpa only [hs] using hcorrection)
  · cases hcorrection

end PaperProofs.Retained.PRetDelayedPolicy010
