module

public import PaperProofs.Common.ReferenceBudgetReplay

/-!
Initial-availability parameterization of the same finite reference replay.
The cache, visible queries, and native ledger are reused. Excluded tools occur
only in a finite rank argument, never as commitments, execution records, or
synthetic visible events. The univ instance exactly recovers the old replay.
Native Prefix alignment and controller performance remain separate obligations.
-/
@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}

/-- A rank argument only; these excluded tools are not ledger commitments. -/
def referenceRankExcluded (I : Instance) (initialAvailable used : Finset I.Tool) : Finset I.Tool :=
  (Finset.univ \ initialAvailable) ∪ used

theorem referenceRank_remaining (I : Instance) (initialAvailable used : Finset I.Tool) :
    Finset.univ \ referenceRankExcluded I initialAvailable used = initialAvailable \ used := by
  ext tool
  simp [referenceRankExcluded]

@[simp] theorem referenceRankExcluded_univ (I : Instance) (used : Finset I.Tool) :
    referenceRankExcluded I Finset.univ used = used := by simp [referenceRankExcluded]

def referenceAvailableRankCase (I : Instance) (initialAvailable : Finset I.Tool)
    (stage : I.Stage) (used : Finset I.Tool) : Option ReferenceBudgetCase :=
  referenceRankCase I stage (referenceRankExcluded I initialAvailable used)

def referenceAvailableRepairTool (I : Instance) (initialAvailable : Finset I.Tool)
    (stage : I.Stage) (used : Finset I.Tool) : Option I.Tool :=
  referenceRepairTool I stage (referenceRankExcluded I initialAvailable used)

@[simp] theorem referenceAvailableRankCase_univ (I : Instance) (stage : I.Stage) (used : Finset I.Tool) :
    referenceAvailableRankCase I Finset.univ stage used = referenceRankCase I stage used := by
  simp only [referenceAvailableRankCase, referenceRankExcluded_univ]

@[simp] theorem referenceAvailableRepairTool_univ (I : Instance) (stage : I.Stage) (used : Finset I.Tool) :
    referenceAvailableRepairTool I Finset.univ stage used = referenceRepairTool I stage used := by
  simp only [referenceAvailableRepairTool, referenceRankExcluded_univ]

theorem referenceAvailableRankCase_exists (I : Instance) (initialAvailable : Finset I.Tool)
    (stage : I.Stage) (used : Finset I.Tool) :
    ∃ kind, referenceAvailableRankCase I initialAvailable stage used = some kind :=
  referenceRankCase_exists I stage _

theorem referenceAvailableRankCase_semantics (I : Instance) (initialAvailable : Finset I.Tool)
    (stage : I.Stage) (used : Finset I.Tool) (kind : ReferenceBudgetCase)
    (hcase : referenceAvailableRankCase I initialAvailable stage used = some kind) :
    match kind with
    | .infiniteRank => PaperProofs.Structure.errorRank (I.compatibility.drop stage.val) (initialAvailable \ used) = ⊤
    | .noTool => PaperProofs.Structure.errorRank (I.compatibility.drop stage.val) (initialAvailable \ used) ≠ ⊤ ∧
        I.eligible stage ∩ (initialAvailable \ used) = ∅
    | .finiteBad depth => PaperProofs.Structure.errorRank (I.compatibility.drop stage.val) (initialAvailable \ used) ≠ ⊤ ∧
        PaperProofs.Structure.badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1))
          (initialAvailable \ used) = depth.val := by
  have h := referenceRankCase_semantics I stage (referenceRankExcluded I initialAvailable used) kind hcase
  cases kind <;> simpa only [referenceRank_remaining] using h

theorem referenceAvailableRepairTool_spec (I : Instance) (initialAvailable : Finset I.Tool)
    (stage : I.Stage) (used : Finset I.Tool) (tool : I.Tool)
    (hsel : referenceAvailableRepairTool I initialAvailable stage used = some tool) :
    tool ∈ I.eligible stage ∩ (initialAvailable \ used) ∧
      PaperProofs.Structure.errorRank (I.compatibility.drop (stage.val + 1)) ((initialAvailable \ used).erase tool) =
        PaperProofs.Structure.badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) (initialAvailable \ used) := by
  have hpick : PaperProofs.Structure.pickGenericMaxRankTool I.toolCount (I.eligible stage)
      (I.compatibility.drop (stage.val + 1)) (initialAvailable \ used) = some tool := by
    simpa only [referenceAvailableRepairTool, referenceRepairTool, referenceRank_remaining] using hsel
  exact PaperProofs.Structure.pickGenericMaxRankTool_spec I.toolCount _ _ _ tool hpick

def referenceAvailableKind (I : Instance) (initialAvailable : Finset I.Tool)
    (cache : ReferenceReplayCache I) : Option ReferenceBudgetCase := do
  let stage ← referenceReplayStage I cache
  referenceAvailableRankCase I initialAvailable stage (historyUsed cache.entryHistory)

def referenceAvailableCacheTarget (I : Instance) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (cache : ReferenceReplayCache I) : Option ℚ := do
  if cache.halted || decide (cache.phase ≠ .testing) then none else do
  let kind ← referenceAvailableKind I initialAvailable cache
  let current ← referenceReplayRisk risk cache
  if 0 < current ∧ current ≤ 1 / 4 ∧ cache.events.length ≤ I.stageCount then
    referenceBudgetTarget kind current else none

def referenceAvailableStep (input : StatisticalInput I) (initialAvailable : Finset I.Tool) (risk : ℚ)
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
        referenceAvailableRepairTool I initialAvailable stage (historyUsed cache.entryHistory) = some tool then
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

def referenceAvailableReplay (input : StatisticalInput I) (initialAvailable : Finset I.Tool) (risk : ℚ)
    (history : List (VisibleEvent I)) : Option (ReferenceReplayCache I) := do
  if 0 < risk ∧ risk ≤ 1 / 2 then pure () else none
  let cache ← history.foldlM (referenceAvailableStep input initialAvailable risk) (referenceReplayInitial I)
  if cache.phase ≠ .written ∧ cache.events.length ≤ I.stageCount ∧
      historyCursor cache.seen ≤ I.stageCount ∧ cache.seen = history then some cache else none

def referenceAvailableEntryTarget (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (history : List (VisibleEvent I)) : Option ℚ := do
  let cache ← referenceAvailableReplay input initialAvailable risk history
  referenceAvailableCacheTarget I initialAvailable risk cache

@[simp] theorem referenceAvailableKind_univ (I : Instance) (cache : ReferenceReplayCache I) :
    referenceAvailableKind I Finset.univ cache = referenceReplayKind I cache := by
  simp only [referenceAvailableKind, referenceReplayKind, referenceAvailableRankCase_univ]

@[simp] theorem referenceAvailableCacheTarget_univ (I : Instance) (risk : ℚ) (cache : ReferenceReplayCache I) :
    referenceAvailableCacheTarget I Finset.univ risk cache = referenceCacheTarget I risk cache := by
  simp only [referenceAvailableCacheTarget, referenceCacheTarget, referenceAvailableKind_univ]

theorem referenceAvailableStep_univ (input : StatisticalInput I) (risk : ℚ)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) :
    referenceAvailableStep input Finset.univ risk cache event = referenceReplayStep input risk cache event := by
  cases event <;> simp only [referenceAvailableStep, referenceReplayStep, referenceAvailableKind_univ,
    referenceAvailableCacheTarget_univ, referenceAvailableRepairTool_univ, Finset.mem_univ, true_and]

theorem referenceAvailableReplay_univ (input : StatisticalInput I) (risk : ℚ) (history : List (VisibleEvent I)) :
    referenceAvailableReplay input Finset.univ risk history = referenceReplay input risk history := by
  have hstep : referenceAvailableStep input Finset.univ risk = referenceReplayStep input risk := by
    funext cache event
    exact referenceAvailableStep_univ input risk cache event
  simp only [referenceAvailableReplay, referenceReplay, hstep]

theorem referenceAvailableEntryTarget_univ (input : StatisticalInput I) (risk : ℚ) (history : List (VisibleEvent I)) :
    referenceAvailableEntryTarget input Finset.univ risk history = referenceEntryTarget input risk history := by
  simp only [referenceAvailableEntryTarget, referenceEntryTarget, referenceAvailableReplay_univ,
    referenceAvailableCacheTarget_univ]

end PaperProofs.Common.Native

