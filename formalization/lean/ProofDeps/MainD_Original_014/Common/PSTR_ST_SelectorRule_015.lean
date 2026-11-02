module

public import Common.PSTR_ST_Selector_014

/-! Statistical max-selector reference interpreter. The actual table instance
is proved equal to its unchanged original table rule at the SAME cache/tool.
No generic-picker run equality or runtime oracle is postulated. This auxiliary
interpreter is for variable-fee analysis, not a new physical-machine input. -/

@[expose] public section

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector

open PaperProofs.Structure.LaminarTree CompactPrice

variable {I : Instance}

def step (choose : Selector I) (input : StatisticalInput I) (initialAvailable : Finset I.Tool) (risk : ℚ)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) : Option (ReferenceReplayCache I) :=
  if cache.halted then none else
  let recorded := { cache with seen := cache.seen ++ [event] }
  match event with
  | .observation i symbol => do
    let stage ← referenceReplayStage I cache
    if i = stage ∧ symbol < (input.experiment i).alphabetSize ∧ cache.phase = .testing ∧
        (referenceAvailableCacheTarget I initialAvailable risk cache).isSome then some recorded else none
  | .wrote i _ serial => do
    let stage ← referenceReplayStage I cache
    let _kind ← referenceAvailableKind I initialAvailable cache
    let _current ← referenceReplayRisk risk cache
    if i = stage ∧ serial = (historyActions cache.seen).length ∧ cache.phase = .testing then
      some { recorded with phase := .written } else none
  | .report i truth serial => do
    let stage ← referenceReplayStage I cache
    let written ← historyWrite cache.seen stage
    let kind ← referenceAvailableKind I initialAvailable cache
    let _current ← referenceReplayRisk risk cache
    if i = stage ∧ serial = written.2 ∧ cache.phase = .written ∧ cache.events.length < I.stageCount then
      some { recorded with events := cache.events ++ [(kind, decide (written.1 ≠ truth))], phase := .reported }
    else none
  | .committed handle tool => do
    let stage ← referenceReplayStage I cache
    let _current ← referenceReplayRisk risk cache
    if cache.phase = .reported ∧ referenceReplayMismatch cache stage handle ∧
        tool ∈ I.eligible stage ∧ tool ∉ historyUsed cache.seen ∧ tool ∈ initialAvailable ∧
        choose stage (historyUsed cache.entryHistory) = some tool then
      some { recorded with phase := .allocated tool } else none
  | .executed handle tool => do
    let stage ← referenceReplayStage I cache
    if cache.phase = .allocated tool ∧ referenceReplayMismatch cache stage handle then
      some { recorded with phase := .executed tool } else none
  | .advanced i => do
    let stage ← referenceReplayStage I cache
    let _current ← referenceReplayRisk risk cache
    if i = stage ∧ ((cache.phase = .reported ∧ referenceReplayCorrect cache stage) ∨
        ∃ tool, cache.phase = .executed tool) then
      some { recorded with entryHistory := recorded.seen, phase := .testing } else none
  | .stopped =>
    if historyCursor cache.seen = I.stageCount ∧ cache.phase = .testing then
      some { recorded with halted := true } else none
  | .abandoned =>
    if cache.phase ≠ .written then some { recorded with halted := true } else none

def replay (choose : Selector I) (input : StatisticalInput I) (initialAvailable : Finset I.Tool) (risk : ℚ)
    (history : List (VisibleEvent I)) : Option (ReferenceReplayCache I) := do
  if 0 < risk ∧ risk ≤ 1 / 2 then pure () else none
  let cache ← history.foldlM (step choose input initialAvailable risk) (referenceReplayInitial I)
  if cache.phase ≠ .written ∧ cache.events.length ≤ I.stageCount ∧
      historyCursor cache.seen ≤ I.stageCount ∧ cache.seen = history then some cache else none

def candidate (choose : Selector I) (input : StatisticalInput I) (initialAvailable : Finset I.Tool) (risk : ℚ) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) : Action I :=
  match replay choose input initialAvailable risk history with
  | none => .abandon
  | some cache =>
    if cache.halted then .stop else
    match referenceReplayStage I cache with
    | none => if historyCursor history = I.stageCount then .stop else .abandon
    | some stage =>
      match cache.phase with
      | .testing => referenceTestingAction input initialAvailable risk limit cache stage
      | .written => .abandon
      | .reported =>
        if referenceReplayCorrect cache stage then .advance stage else
        match referenceReplayRisk risk cache, referenceVisibleHandle history stage,
            choose stage (historyUsed cache.entryHistory) with
        | some _, some handle, some tool => .allocate handle tool
        | _, _, _ => .abandon
      | .allocated tool =>
        match referenceVisibleHandle history stage with
        | none => .abandon
        | some handle => .execute handle tool
      | .executed _ => .advance stage

def rule (choose : Selector I) (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (limit : ReferenceObservationLimit I) : PolicyRule I Unit := fun _ history =>
  let action := candidate choose input available budget limit history
  if historyAllowsAction history action then action else .abandon

theorem step_table (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility)
    (available : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I) (event : VisibleEvent I) :
    step (table I available) input available budget cache event = tableStep input available budget cache event := by
  have hk := (PSTRStatistics.callbackFormulaClaims I hlaminar available cache budget).1
  have ht := (PSTRStatistics.callbackFormulaClaims I hlaminar available cache budget).2
  unfold step tableStep
  rw [← hk, ← ht]
  rfl

theorem replay_table (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility)
    (available : Finset I.Tool) (budget : ℚ) (history : List (VisibleEvent I)) :
    replay (table I available) input available budget history = tableReplay input available budget history := by
  have hs : step (table I available) input available budget = tableStep input available budget := by
    funext cache event
    exact step_table input hlaminar available budget cache event
  unfold replay tableReplay
  rw [hs]

theorem testing_table (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility)
    (available : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (stage : I.Stage) :
    referenceTestingAction input available budget limit cache stage = tableTestingAction input available budget limit cache stage := by
  have hk := (PSTRStatistics.callbackFormulaClaims I hlaminar available cache budget).1
  have ht := (PSTRStatistics.callbackFormulaClaims I hlaminar available cache budget).2
  unfold referenceTestingAction tableTestingAction
  rw [← hk, ← ht]
  rfl

theorem candidate_table (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility)
    (available : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) :
    candidate (table I available) input available budget limit history = tableCandidate input available budget limit history := by
  have ht : referenceTestingAction input available budget limit = tableTestingAction input available budget limit := by
    funext cache stage
    exact testing_table input hlaminar available budget limit cache stage
  unfold candidate tableCandidate
  rw [replay_table input hlaminar available budget history, ht]
  rfl

theorem rule_table (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility)
    (available : Finset I.Tool) (budget : ℚ) (limit : ReferenceObservationLimit I) :
    rule (table I available) input available budget limit = tableRule input available budget limit := by
  funext seed history
  unfold rule tableRule
  rw [candidate_table input hlaminar available budget limit history]

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector
