module

public import PaperProofs.Paid.PDROC_OverlaySimulator_007
public import PaperProofs.Paid.PDROC_SimulatorLaw_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

theorem overlay_allowed_exit_of_no_ghost (history : List (VisibleEvent I))
    (stage : I.Stage) (action : Action I)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage ≠ none)
    (ha : historyAllowsAction history action)
    (hn : overlayGhostCallOfAction history action = none) :
    action = .advance stage ∨ action = .stop ∨ action = .abandon := by
  cases action with
  | review target =>
    have hs : target = stage := Fin.ext (ha.1.symm.trans hc)
    subst target
    exact False.elim (hw ha.2)
  | write target bit =>
    have hs : target = stage := Fin.ext (ha.1.symm.trans hc)
    subst target
    exact False.elim (hw ha.2)
  | advance target =>
    have hs : target = stage := Fin.ext (ha.1.symm.trans hc)
    exact Or.inl (congrArg Action.advance hs)
  | allocate handle tool => simp [overlayGhostCallOfAction, ha] at hn
  | execute handle tool => simp [overlayGhostCallOfAction, ha] at hn
  | stop => exact Or.inr (Or.inl rfl)
  | abandon => exact Or.inr (Or.inr rfl)

theorem overlay_firstGhost_reserves_current (history : List (VisibleEvent I))
    (stage : I.Stage) (action : Action I) (call : OverlayGhostCall I)
    (hc : historyCursor history = stage.val)
    (hfresh : ∀ pair ∈ historyCommitments history, pair.1.stage ≠ stage)
    (hcall : overlayGhostCallOfAction history action = some call) :
    call.1 = true ∧ call.2.1.stage = stage := by
  obtain ⟨haction, ha⟩ := overlayGhostCallOfAction_some history action call hcall
  rcases call with ⟨reserve, handle, tool⟩
  cases reserve with
  | false =>
    simp only [overlayGhostAction, Bool.false_eq_true, ↓reduceIte] at haction
    rw [haction] at ha
    rcases ha with ⟨hc', _, _, hm, _, _⟩
    exact False.elim (hfresh _ hm (Fin.ext (hc'.symm.trans hc)))
  | true =>
    simp only [overlayGhostAction, ↓reduceIte] at haction
    rw [haction] at ha
    exact ⟨rfl, Fin.ext (ha.1.symm.trans hc)⟩

theorem overlay_committedGhost_executes_current (history : List (VisibleEvent I))
    (stage : I.Stage) (action : Action I) (call : OverlayGhostCall I)
    (hc : historyCursor history = stage.val)
    (hcommit : ∃ pair ∈ historyCommitments history, pair.1.stage = stage)
    (hcall : overlayGhostCallOfAction history action = some call) :
    call.1 = false ∧ call.2.1.stage = stage := by
  obtain ⟨haction, ha⟩ := overlayGhostCallOfAction_some history action call hcall
  rcases call with ⟨reserve, handle, tool⟩
  cases reserve with
  | false =>
    simp only [overlayGhostAction, Bool.false_eq_true, ↓reduceIte] at haction
    rw [haction] at ha
    exact ⟨rfl, Fin.ext (ha.1.symm.trans hc)⟩
  | true =>
    simp only [overlayGhostAction, ↓reduceIte] at haction
    rw [haction] at ha
    rcases ha with ⟨hc', _, _, _, hno⟩
    obtain ⟨pair, hm, hs⟩ := hcommit
    exact False.elim (hno pair hm (hs.trans (Fin.ext (hc'.symm.trans hc)).symm))

theorem overlay_allowed_exit_of_committed_executed (history : List (VisibleEvent I))
    (stage : I.Stage) (action : Action I)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage ≠ none)
    (ha : historyAllowsAction history action)
    (hcommit : ∃ pair ∈ historyCommitments history, pair.1.stage = stage)
    (hexecute : ∃ pair ∈ historyExecutions history, pair.1.stage = stage) :
    action = .advance stage ∨ action = .stop ∨ action = .abandon := by
  cases action with
  | review target =>
    have hs : target = stage := Fin.ext (ha.1.symm.trans hc)
    subst target
    exact False.elim (hw ha.2)
  | write target bit =>
    have hs : target = stage := Fin.ext (ha.1.symm.trans hc)
    subst target
    exact False.elim (hw ha.2)
  | advance target =>
    have hs : target = stage := Fin.ext (ha.1.symm.trans hc)
    exact Or.inl (congrArg Action.advance hs)
  | allocate handle tool =>
    rcases ha with ⟨hc', _, _, _, hno⟩
    obtain ⟨pair, hm, hs⟩ := hcommit
    exact False.elim (hno pair hm (hs.trans (Fin.ext (hc'.symm.trans hc)).symm))
  | execute handle tool =>
    rcases ha with ⟨hc', _, _, _, _, hno⟩
    obtain ⟨pair, hm, hs⟩ := hexecute
    exact False.elim (hno pair hm (hs.trans (Fin.ext (hc'.symm.trans hc)).symm))
  | stop => exact Or.inr (Or.inl rfl)
  | abandon => exact Or.inr (Or.inr rfl)

end PDROC

