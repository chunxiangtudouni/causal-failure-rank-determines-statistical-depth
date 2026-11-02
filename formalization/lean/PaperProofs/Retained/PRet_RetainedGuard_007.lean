module

public import PaperProofs.Common.ReferenceController

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetRetainedGuard007

open Common Common.Native MeasureTheory

variable {I : Instance}

/-- The old shared guard enforces the current-allocation window even when
the actual retained contract permits a terminal allocation. This theorem
identifies the encoding issue without assuming a performance claim. -/
theorem current_guard_rejects_terminal_allocate (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (tool : I.Tool) (hcursor : historyCursor history = I.stageCount) :
    ¬ historyAllowsAction history (.allocate handle tool) := by
  intro hallow
  have hsame := hallow.1
  rw [hcursor] at hsame
  exact (Nat.ne_of_lt handle.stage.isLt) hsame.symm

theorem current_guard_rejects_terminal_execute (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (tool : I.Tool) (hcursor : historyCursor history = I.stageCount) :
    ¬ historyAllowsAction history (.execute handle tool) := by
  intro hallow
  have hsame := hallow.1
  rw [hcursor] at hsame
  exact (Nat.ne_of_lt handle.stage.isLt) hsame.symm

/-- Original retained permissions: reported actual write handle, compatible
tool, single allocation per stage/tool, and a genuine unused commitment for
execution. No current-cursor equality is imposed on terminal corrections. -/
def allows (history : List (VisibleEvent I)) : Action I → Prop
  | .allocate handle tool => historyValidHandle history handle ∧ tool ∈ I.eligible handle.stage ∧
      tool ∉ historyUsed history ∧ ∀ pair ∈ historyCommitments history, pair.1.stage ≠ handle.stage
  | .execute handle tool => historyValidHandle history handle ∧ tool ∈ I.eligible handle.stage ∧
      (handle, tool) ∈ historyCommitments history ∧
      (∀ pair ∈ historyExecutions history, pair.2 ≠ tool) ∧
      (∀ pair ∈ historyExecutions history, pair.1.stage ≠ handle.stage)
  | action => historyAllowsAction history action

instance allows_decidable (history : List (VisibleEvent I)) (action : Action I) : Decidable (allows history action) := by
  cases action <;> dsimp only [allows] <;> infer_instance

theorem historyValidHandle_complete (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s) (handle : MismatchHandle I)
    (hhandle : validHandle s handle) : historyValidHandle s.history handle := by
  obtain ⟨hwrong, hserial, time, hreported⟩ := hhandle
  unfold historyValidHandle
  rw [prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp handle.stage,
    hreported, Option.map_some]
  rw [prefix_historyWritten input C mode accounting rule seed truth tapes hp handle.stage,
    prefix_historyWriteSerial input C mode accounting rule seed truth tapes hp handle.stage]
  exact ⟨hwrong, hserial, hserial.symm⟩

/-- Completeness on actual Prefixes, including terminal cursor=N: every
genuine legal correction Step is admitted by the corrected public guard.
Thus a legal terminalMatchingAction is never rejected solely by its stage
being behind the terminal cursor. -/
theorem allows_of_step (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) {Seed : Type*} (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s next : State I} {action : Action I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes n s)
    (hs : Step input C .uncapped accounting tapes s action next) : allows s.history action := by
  cases hs with
  | review _ live port _ =>
    exact ⟨(prefix_historyCursor input C .uncapped accounting rule seed truth tapes hp).trans live.2,
      (prefix_historyWritten input C .uncapped accounting rule seed truth tapes hp _).trans port⟩
  | write _ _ live port _ =>
    exact ⟨(prefix_historyCursor input C .uncapped accounting rule seed truth tapes hp).trans live.2,
      (prefix_historyWritten input C .uncapped accounting rule seed truth tapes hp _).trans port⟩
  | advance _ live written _ =>
    refine ⟨(prefix_historyCursor input C .uncapped accounting rule seed truth tapes hp).trans live.2, ?_⟩
    simpa only [prefix_historyWritten input C .uncapped accounting rule seed truth tapes hp _] using written
  | allocate handle tool _ hhandle hcompatible hunused hunallocated _ _ =>
    refine ⟨historyValidHandle_complete input C hearly .uncapped accounting rule seed truth tapes hp handle hhandle,
      hcompatible, (prefix_historyUnused_iff input C .uncapped accounting rule seed truth tapes hp tool).mpr hunused, ?_⟩
    intro pair hpair
    rw [prefix_historyCommitments input C .uncapped accounting rule seed truth tapes hp] at hpair
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hpair
    exact hunallocated a ha
  | execute handle tool _ hhandle hcompatible hcommit hunused huncorrected _ _ =>
    refine ⟨historyValidHandle_complete input C hearly .uncapped accounting rule seed truth tapes hp handle hhandle,
      hcompatible, ?_, ?_, ?_⟩
    · obtain ⟨a, ha, hh, ht⟩ := hcommit
      rw [prefix_historyCommitments input C .uncapped accounting rule seed truth tapes hp]
      exact List.mem_map.mpr ⟨a, ha, by simp only [hh, ht]⟩
    · intro pair hpair
      rw [prefix_historyExecutions input C .uncapped accounting rule seed truth tapes hp] at hpair
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpair
      exact hunused e he
    · intro pair hpair
      rw [prefix_historyExecutions input C .uncapped accounting rule seed truth tapes hp] at hpair
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpair
      exact huncorrected e he
  | stop => trivial
  | abandon => trivial

theorem allows_sound (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) {Seed : Type*} (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting rule seed truth tapes n s)
    (hactive : s.halted = false) (action : Action I) (hallow : allows s.history action) :
    ∃ next, Step input C .uncapped accounting tapes s action next := by
  cases action with
  | allocate handle tool =>
    obtain ⟨hvalid, hcompatible, hunused, hstage⟩ := hallow
    have hv := historyValidHandle_sound input C hretained.1 .uncapped accounting rule seed truth tapes hp handle hvalid
    have hu := (prefix_historyUnused_iff input C .uncapped accounting rule seed truth tapes hp tool).mp hunused
    have hs : ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ handle.stage := by
      intro a ha
      apply hstage (a.handle, a.tool)
      rw [prefix_historyCommitments input C .uncapped accounting rule seed truth tapes hp]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
    refine ⟨_, .allocate s handle tool hactive hv hcompatible hu hs ?_ (.inl rfl)⟩
    simp [allocationOpen, hretained.2.1]
  | execute handle tool =>
    obtain ⟨hvalid, hcompatible, hcommit, hunused, hstage⟩ := hallow
    have hv := historyValidHandle_sound input C hretained.1 .uncapped accounting rule seed truth tapes hp handle hvalid
    have hc : ∃ a ∈ s.ledger.commitments, a.handle = handle ∧ a.tool = tool := by
      rw [prefix_historyCommitments input C .uncapped accounting rule seed truth tapes hp] at hcommit
      obtain ⟨a, ha, heq⟩ := List.mem_map.mp hcommit
      exact ⟨a, ha, congrArg Prod.fst heq, congrArg Prod.snd heq⟩
    have hu : ∀ e ∈ s.ledger.executions, e.tool ≠ tool := by
      intro e he
      apply hunused (e.handle, e.tool)
      rw [prefix_historyExecutions input C .uncapped accounting rule seed truth tapes hp]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    have hs : ∀ e ∈ s.ledger.executions, e.handle.stage ≠ handle.stage := by
      intro e he
      apply hstage (e.handle, e.tool)
      rw [prefix_historyExecutions input C .uncapped accounting rule seed truth tapes hp]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    refine ⟨_, .execute s handle tool hactive hv hcompatible hc hu hs ?_ (.inl rfl)⟩
    simp [executionOpen, hretained.2.2]
  | review stage => exact historyAllowsAction_sound input C hretained.1 accounting rule seed truth tapes hp hactive _ hallow
  | write stage bit => exact historyAllowsAction_sound input C hretained.1 accounting rule seed truth tapes hp hactive _ hallow
  | advance stage => exact historyAllowsAction_sound input C hretained.1 accounting rule seed truth tapes hp hactive _ hallow
  | stop => exact ⟨_, .stop s hactive⟩
  | abandon => exact ⟨_, .abandon s hactive⟩

def guarded {Seed : Type*} (raw : PolicyRule I Seed) : PolicyRule I Seed := fun seed history =>
  if allows history (raw seed history) then raw seed history else .abandon

theorem guarded_action_of_step (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) {Seed : Type*} (raw : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s next : State I}
    (hp : Prefix input C .uncapped accounting (guarded raw) seed truth tapes n s)
    (hs : Step input C .uncapped accounting tapes s (raw seed s.history) next) :
    guarded raw seed s.history = raw seed s.history := by
  have hallow := allows_of_step input C hearly accounting (guarded raw) seed truth tapes hp hs
  exact ite_eq_left hallow

theorem guarded_legal (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) {Seed : Type*} (raw : PolicyRule I Seed) :
    LegalRule input C .uncapped accounting (guarded raw) := by
  intro seed truth tapes n s hp hactive
  by_cases hallow : allows s.history (raw seed s.history)
  · obtain ⟨next, hs⟩ := allows_sound input C hretained accounting (guarded raw) seed truth tapes hp hactive _ hallow
    exact ⟨next, by simpa only [guarded, hallow, ↓reduceIte] using hs⟩
  · exact ⟨stopState s true, by simpa only [guarded, hallow, ↓reduceIte] using
      (Step.abandon (input := input) (C := C) (mode := ResourceMode.uncapped) (accounting := accounting) (tapes := tapes) s hactive)⟩

theorem measurable_guarded {Seed : Type*} [MeasurableSpace Seed] (raw : PolicyRule I Seed)
    (hraw : MeasurableRule raw) : MeasurableRule (guarded raw) := by
  exact (measurable_of_countable (fun pair : List (VisibleEvent I) × Action I =>
    if allows pair.1 pair.2 then pair.2 else .abandon)).comp (measurable_snd.prodMk hraw)

end PaperProofs.Retained.PRetRetainedGuard007
