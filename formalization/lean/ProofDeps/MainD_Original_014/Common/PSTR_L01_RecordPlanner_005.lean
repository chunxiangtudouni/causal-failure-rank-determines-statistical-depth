module

public import Common.PSTR_TM_L01_CacheRecord_252b

/-! Record-only action semantics from the actually reconstructed cache.
This component reads no incidence/rank function. The following local
refinement equalities will be discharged by the actual Prefix producer252,
not added to the ORIGINAL planner's input or qualification. A full Bool
history parser, numeric quota producer and paid scalar calls remain needed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTableRecordPlanner

open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRTML01CacheRecord252

variable {I : Instance}

def recordTarget (risk : ℚ) (records : List Nat) (cache : ReferenceReplayCache I) : Option ℚ :=
  if cache.halted || decide (cache.phase ≠ .testing) then none else do
    let kind ← recordKindAtCache records cache
    let current ← referenceReplayRisk risk cache
    if 0 < current ∧ current ≤ 1 / 4 ∧ cache.events.length ≤ I.stageCount then
      referenceBudgetTarget kind current else none

def recordTestingAction (input : StatisticalInput I) (risk : ℚ) (limit : ReferenceObservationLimit I)
    (records : List Nat) (cache : ReferenceReplayCache I) (stage : I.Stage) : Action I :=
  match recordKindAtCache records cache with
  | none => .abandon
  | some .infiniteRank => .write stage false
  | some .noTool | some (.finiteBad _) =>
    match recordTarget risk records cache with
    | none => .abandon
    | some target =>
      if hvalid : ∀ symbol ∈ historyObservations cache.seen stage,
          symbol < (input.experiment stage).alphabetSize then
        let word := historyObservationWord input cache.seen stage hvalid
        if (input.experiment stage).rationalWordHits target word then
          .write stage ((input.experiment stage).rationalWordMAP word)
        else match limit with
          | none => .review stage
          | some quota => if (historyObservations cache.seen stage).length < quota stage then .review stage else .abandon
      else .abandon

def recordCandidateFromCache (input : StatisticalInput I) (risk : ℚ) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (records : List Nat) (cache : ReferenceReplayCache I) : Action I :=
  if cache.halted then .stop else
  match referenceReplayStage I cache with
  | none => if historyCursor history = I.stageCount then .stop else .abandon
  | some stage =>
    match cache.phase with
    | .testing => recordTestingAction input risk limit records cache stage
    | .written => .abandon
    | .reported =>
      if referenceReplayCorrect cache stage then .advance stage else
      match referenceReplayRisk risk cache, referenceVisibleHandle history stage, recordToolAtCache records cache with
      | some _, some handle, some tool => .allocate handle tool
      | _, _, _ => .abandon
    | .allocated tool =>
      match referenceVisibleHandle history stage with
      | none => .abandon
      | some handle => .execute handle tool
    | .executed _ => .advance stage

def recordRuleFromCache (input : StatisticalInput I) (risk : ℚ) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (records : List Nat) (cache : ReferenceReplayCache I) : Action I :=
  let action := recordCandidateFromCache input risk limit history records cache
  if historyAllowsAction history action then action else .abandon

theorem record_target_eq (available : Finset I.Tool) (risk : ℚ) (records : List Nat)
    (cache : ReferenceReplayCache I)
    (kind : recordKindAtCache records cache = tableKind I available cache) :
    recordTarget risk records cache = tableTarget I available risk cache := by
  unfold recordTarget tableTarget
  rw [kind]

theorem record_testing_eq (input : StatisticalInput I) (available : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) (records : List Nat)
    (cache : ReferenceReplayCache I) (stage : I.Stage)
    (kind : recordKindAtCache records cache = tableKind I available cache) :
    recordTestingAction input risk limit records cache stage =
      tableTestingAction input available risk limit cache stage := by
  unfold recordTestingAction tableTestingAction
  rw [kind, record_target_eq available risk records cache kind]
  rfl

theorem record_candidate_eq (input : StatisticalInput I) (available : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I))
    (records : List Nat) (cache : ReferenceReplayCache I)
    (parsed : tableReplay input available risk history = some cache)
    (kind : recordKindAtCache records cache = tableKind I available cache)
    (tool : recordToolAtCache records cache = tableToolAtCache available cache) :
    recordCandidateFromCache input risk limit history records cache =
      tableCandidate input available risk limit history := by
  unfold recordCandidateFromCache tableCandidate
  rw [parsed]
  by_cases stopped : cache.halted = true
  · simp only [stopped, ite_true]
  · have live : cache.halted = false := Bool.eq_false_of_not_eq_true stopped
    simp only [live, Bool.false_eq_true, ite_false]
    cases selected : referenceReplayStage I cache with
    | none => rfl
    | some stage =>
      cases phase : cache.phase with
      | testing => exact record_testing_eq input available risk limit records cache stage kind
      | written => rfl
      | reported =>
        have chosen : recordToolAtCache records cache =
            (tableReply I available stage (historyUsed cache.entryHistory)).tool := by
          rw [tool, tableToolAtCache, selected, Option.bind_some]
        rw [chosen]
        rfl
      | allocated selectedTool => rfl
      | executed selectedTool => rfl

theorem record_rule_eq (input : StatisticalInput I) (available : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I))
    (records : List Nat) (cache : ReferenceReplayCache I)
    (parsed : tableReplay input available risk history = some cache)
    (kind : recordKindAtCache records cache = tableKind I available cache)
    (tool : recordToolAtCache records cache = tableToolAtCache available cache) :
    recordRuleFromCache input risk limit history records cache =
      tableRule input available risk limit () history := by
  unfold recordRuleFromCache tableRule
  rw [record_candidate_eq input available risk limit history records cache parsed kind tool]

end PaperProofs.Common.Native.PSTRTableRecordPlanner
