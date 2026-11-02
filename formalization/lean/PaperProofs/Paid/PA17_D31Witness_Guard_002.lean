module

public import PaperProofs.Retained.PRet_RetainedGuard_007
public import PaperProofs.Common.NativeCapTransfer
public import PaperProofs.Paid.BridgeClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessGuard002

open Common Common.Native MeasureTheory

variable {I : Instance}

def mixedAllows (history : List (VisibleEvent I)) : Action I → Prop
  | .execute handle tool => Retained.PRetRetainedGuard007.allows history (.execute handle tool)
  | action => historyAllowsAction history action

instance mixedAllows_decidable (history : List (VisibleEvent I)) (action : Action I) :
    Decidable (mixedAllows history action) := by
  cases action <;> dsimp only [mixedAllows] <;> infer_instance

theorem mixedAllows_sound (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hexecution : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) {Seed : Type*} (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting rule seed truth tapes n s)
    (hactive : s.halted = false) (action : Action I) (hallow : mixedAllows s.history action) :
    ∃ next, Step input C .uncapped accounting tapes s action next := by
  cases action with
  | execute handle tool =>
    obtain ⟨hvalid, hcompatible, hcommit, hunused, hstage⟩ := hallow
    have hv := historyValidHandle_sound input C hearly .uncapped accounting rule seed truth tapes hp handle hvalid
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
    simp [executionOpen, hexecution]
  | review stage => exact historyAllowsAction_sound input C hearly accounting rule seed truth tapes hp hactive _ hallow
  | write stage bit => exact historyAllowsAction_sound input C hearly accounting rule seed truth tapes hp hactive _ hallow
  | advance stage => exact historyAllowsAction_sound input C hearly accounting rule seed truth tapes hp hactive _ hallow
  | allocate handle tool => exact historyAllowsAction_sound input C hearly accounting rule seed truth tapes hp hactive _ hallow
  | stop => exact ⟨_, .stop s hactive⟩
  | abandon => exact ⟨_, .abandon s hactive⟩

def mixedGuarded {Seed : Type*} (raw : PolicyRule I Seed) : PolicyRule I Seed := fun seed history =>
  if mixedAllows history (raw seed history) then raw seed history else .abandon

theorem mixedGuarded_legal (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hexecution : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) {Seed : Type*} (raw : PolicyRule I Seed) :
    LegalRule input C .uncapped accounting (mixedGuarded raw) := by
  intro seed truth tapes n s hp hactive
  by_cases hallow : mixedAllows s.history (raw seed s.history)
  · obtain ⟨next, hs⟩ := mixedAllows_sound input C hearly hexecution accounting (mixedGuarded raw)
      seed truth tapes hp hactive _ hallow
    exact ⟨next, by simpa only [mixedGuarded, hallow, ↓reduceIte] using hs⟩
  · exact ⟨stopState s true, by simpa only [mixedGuarded, hallow, ↓reduceIte] using
      (Step.abandon (input := input) (C := C) (mode := ResourceMode.uncapped)
        (accounting := accounting) (tapes := tapes) s hactive)⟩

theorem measurable_mixedGuarded {Seed : Type*} [MeasurableSpace Seed] (raw : PolicyRule I Seed)
    (hraw : MeasurableRule raw) : MeasurableRule (mixedGuarded raw) := by
  exact (measurable_of_countable (fun pair : List (VisibleEvent I) × Action I =>
    if mixedAllows pair.1 pair.2 then pair.2 else .abandon)).comp (measurable_snd.prodMk hraw)

theorem mixedAllows_of_step (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s next : State I} {action : Action I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes n s)
    (hs : Step input C .uncapped accounting tapes s action next)
    (hallocate : ∀ handle tool, action = .allocate handle tool → s.cursor = handle.stage.val) :
    mixedAllows s.history action := by
  have ha := Retained.PRetRetainedGuard007.allows_of_step input C hearly accounting
    rule seed truth tapes hp hs
  cases action with
  | allocate handle tool =>
    exact ⟨(prefix_historyCursor input C .uncapped accounting rule seed truth tapes hp).trans
      (hallocate handle tool rfl), ha⟩
  | execute handle tool => exact ha
  | review stage => exact ha
  | write stage bit => exact ha
  | advance stage => exact ha
  | stop => trivial
  | abandon => trivial

theorem mixedGuarded_action_of_step (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    {Seed : Type*} (raw : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s next : State I}
    (hp : Prefix input C .uncapped accounting (mixedGuarded raw) seed truth tapes n s)
    (hs : Step input C .uncapped accounting tapes s (raw seed s.history) next)
    (hallocate : ∀ handle tool, raw seed s.history = .allocate handle tool → s.cursor = handle.stage.val) :
    mixedGuarded raw seed s.history = raw seed s.history := by
  exact ite_eq_left (mixedAllows_of_step input C hearly accounting
    (mixedGuarded raw) seed truth tapes hp hs hallocate)

theorem mixedGuarded_ne_review {Seed : Type*} (raw : PolicyRule I Seed)
    (hnoreview : ∀ seed history stage, raw seed history ≠ .review stage)
    (seed : Seed) (history : List (VisibleEvent I)) (stage : I.Stage) :
    mixedGuarded raw seed history ≠ .review stage := by
  unfold mixedGuarded
  split_ifs
  · exact hnoreview seed history stage
  · simp

theorem mixedGuarded_write_false {Seed : Type*} (raw : PolicyRule I Seed)
    (hfalse : ∀ seed history stage bit, raw seed history = .write stage bit → bit = false)
    (seed : Seed) (history : List (VisibleEvent I)) (stage : I.Stage) (bit : Bool)
    (hwrite : mixedGuarded raw seed history = .write stage bit) : bit = false := by
  unfold mixedGuarded at hwrite
  split_ifs at hwrite
  exact hfalse seed history stage bit hwrite

end PaperProofs.Paid.PA17D31WitnessGuard002
