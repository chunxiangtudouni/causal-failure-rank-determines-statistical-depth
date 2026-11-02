module
public import Common.PSTR_TM_L01_RecordReplay_253b

/-! A record-only replay step. Its executable body has no tableKind,
tableReply, structural rank or eligibility-set lookup. The old laminar
callback theorem discharges eligibility IN THE PROOF whenever a record
tool is selected. Kind/tool equalities below are local simulation facts;
the actual-Prefix fold theorem will derive them, not assume them. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTML01RecordReplay253
open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRStatistics.TableAlignment PSTRTML01CacheRecord252

variable {I : Instance}

def targetFromRecords (risk : Rat) (records : List Nat) (cache : ReferenceReplayCache I) : Option Rat := do
  if cache.halted || decide (cache.phase ≠ .testing) then none else do
  let kind ← recordKindAtCache records cache
  let current ← referenceReplayRisk risk cache
  if 0 < current ∧ current ≤ 1/4 ∧ cache.events.length ≤ I.stageCount then
    referenceBudgetTarget kind current else none

def recordStep (input : StatisticalInput I) (available : Finset I.Tool) (risk : Rat)
    (records : List Nat) (cache : ReferenceReplayCache I) (event : VisibleEvent I) : Option (ReferenceReplayCache I) :=
  if cache.halted then none else
  let recorded := {cache with seen := cache.seen++[event]}
  match event with
  | .observation i symbol => do
    let stage ← referenceReplayStage I cache
    if i = stage ∧ symbol < (input.experiment i).alphabetSize ∧ cache.phase = .testing ∧
        (targetFromRecords risk records cache).isSome then some recorded else none
  | .wrote i _ serial => do
    let stage ← referenceReplayStage I cache
    let _ ← recordKindAtCache records cache
    let _ ← referenceReplayRisk risk cache
    if i = stage ∧ serial = (historyActions cache.seen).length ∧ cache.phase = .testing then
      some {recorded with phase := .written} else none
  | .report i truth serial => do
    let stage ← referenceReplayStage I cache
    let written ← historyWrite cache.seen stage
    let kind ← recordKindAtCache records cache
    let _ ← referenceReplayRisk risk cache
    if i = stage ∧ serial = written.2 ∧ cache.phase = .written ∧ cache.events.length < I.stageCount then
      some {recorded with events := cache.events++[(kind,decide (written.1 ≠ truth))],phase := .reported}
    else none
  | .committed handle tool => do
    let stage ← referenceReplayStage I cache
    let _ ← referenceReplayRisk risk cache
    if cache.phase = .reported ∧ referenceReplayMismatch cache stage handle ∧
        tool ∉ historyUsed cache.seen ∧ tool ∈ available ∧ recordToolAtCache records cache = some tool then
      some {recorded with phase := .allocated tool} else none
  | .executed handle tool => do
    let stage ← referenceReplayStage I cache
    if cache.phase = .allocated tool ∧ referenceReplayMismatch cache stage handle then
      some {recorded with phase := .executed tool} else none
  | .advanced i => do
    let stage ← referenceReplayStage I cache
    let _ ← referenceReplayRisk risk cache
    if i = stage ∧ ((cache.phase = .reported ∧ referenceReplayCorrect cache stage) ∨
        ∃ tool, cache.phase = .executed tool) then
      some {recorded with entryHistory := recorded.seen,phase := .testing} else none
  | .stopped =>
    if historyCursor cache.seen = I.stageCount ∧ cache.phase = .testing then
      some {recorded with halted := true} else none
  | .abandoned =>
    if cache.phase ≠ .written then some {recorded with halted := true} else none

theorem recordStep_eq_tableStep (input : StatisticalInput I) (available : Finset I.Tool)
    (risk : Rat) (records : List Nat) (cache : ReferenceReplayCache I) (event : VisibleEvent I)
    (laminar : LaminarSchedule I.compatibility)
    (kind : recordKindAtCache records cache = tableKind I available cache)
    (tool : recordToolAtCache records cache = tableToolAtCache available cache) :
    recordStep input available risk records cache event = tableStep input available risk cache event := by
  cases event with
  | observation i symbol =>
    simp only [recordStep,tableStep,targetFromRecords,tableTarget,kind]
    rfl
  | wrote i bit serial => simp only [recordStep,tableStep,kind]
  | report i truth serial => simp only [recordStep,tableStep,kind]
  | committed handle chosen =>
    cases stopped : cache.halted with
    | true => simp only [recordStep,tableStep,stopped,ite_true]
    | false =>
      simp only [recordStep,tableStep,stopped,Bool.false_eq_true,ite_false]
      cases position : referenceReplayStage I cache with
      | none => simp only [Option.bind_eq_bind,Option.bind_none]
      | some stage =>
        have selectedEq : recordToolAtCache records cache =
            (tableReply I available stage (historyUsed cache.entryHistory)).tool := by
          rw [tool,tableToolAtCache,position,Option.bind_some]
        simp only [Option.bind_eq_bind,Option.bind_some,selectedEq]
        by_cases selected : (tableReply I available stage (historyUsed cache.entryHistory)).tool = some chosen
        · have eligible : chosen ∈ I.eligible stage :=
            (Finset.mem_inter.mp (tableRepairTool_spec I laminar available stage
              (historyUsed cache.entryHistory) chosen selected).1).1
          simp only [eligible,selected,true_and,and_true]
        · simp only [selected,and_false,ite_false]
  | executed handle chosen => rfl
  | advanced stage => rfl
  | stopped => rfl
  | abandoned => rfl

theorem tableStep_wrote_state (input : StatisticalInput I) (available : Finset I.Tool)
    (risk : Rat) (cache written : ReferenceReplayCache I) (i : I.Stage) (bit : Bool) (serial : Nat)
    (success : tableStep input available risk cache (.wrote i bit serial) = some written) :
    written = afterWrite cache i bit serial := by
  cases stopped : cache.halted with
  | true =>
    simp only [tableStep,stopped,ite_true] at success
    cases success
  | false =>
    simp only [tableStep,stopped,Bool.false_eq_true,ite_false] at success
    cases position : referenceReplayStage I cache with
    | none =>
      simp only [position,Option.bind_eq_bind,Option.bind_none] at success
      cases success
    | some stage =>
      simp only [position,Option.bind_eq_bind,Option.bind_some] at success
      cases kind : tableKind I available cache with
      | none =>
        simp only [kind,Option.bind_none] at success
        cases success
      | some value =>
        simp only [kind,Option.bind_some] at success
        cases current : referenceReplayRisk risk cache with
        | none =>
          simp only [current,Option.bind_none] at success
          cases success
        | some amount =>
          simp only [current,Option.bind_some] at success
          split_ifs at success
          simpa only [afterWrite,stopped] using (Option.some.inj success).symm

end PaperProofs.Common.Native.PSTRTML01RecordReplay253
