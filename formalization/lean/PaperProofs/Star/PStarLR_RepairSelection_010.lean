module

public import PaperProofs.Star.PStarLR_ToolChoice_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

namespace PStarLR

theorem visibleHandle_stage {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage)
    (handle : MismatchHandle I) (visible : referenceVisibleHandle history stage = some handle) :
    handle.stage = stage := by
  unfold referenceVisibleHandle at visible
  cases hw : historyWrite history stage with
  | none => simp [hw] at visible
  | some pair =>
    simp only [hw, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at visible
    exact congrArg MismatchHandle.stage visible.symm

theorem repairAction_allocate_selection (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage)
    (choice : Option (starInstance P.tools order).Tool) (handle : MismatchHandle (starInstance P.tools order))
    (tool : (starInstance P.tools order).Tool)
    (selected : P.repairAction order history stage choice .stop = .allocate handle tool) :
    referenceVisibleHandle history stage = some handle ∧ choice = some tool ∧
      (historyCommitments history).find? (fun pair => pair.1.stage == stage) = none ∧
      (historyExecutions history).any (fun pair => pair.1.stage == stage) = false ∧ handle.stage = stage := by
  unfold Parameters.repairAction at selected
  split at selected
  · cases selected
  · rename_i notExecuted
    have hfalse : (historyExecutions history).any (fun pair => pair.1.stage == stage) = false :=
      Bool.eq_false_iff.mpr notExecuted
    cases hfind : (historyCommitments history).find? (fun pair => pair.1.stage == stage) with
    | some pair => simp only [hfind] at selected; cases selected
    | none =>
      simp only [hfind] at selected
      cases hvisible : referenceVisibleHandle history stage with
      | none => simp only [hvisible] at selected; cases selected
      | some actual =>
        cases hchoice : choice with
        | none => simp only [hchoice, hvisible] at selected; cases selected
        | some chosen =>
          simp only [hchoice, hvisible, Action.allocate.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          exact ⟨rfl, rfl, rfl, hfalse, visibleHandle_stage history stage actual hvisible⟩

theorem repairAction_execute_selection (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage)
    (choice : Option (starInstance P.tools order).Tool) (handle : MismatchHandle (starInstance P.tools order))
    (tool : (starInstance P.tools order).Tool)
    (selected : P.repairAction order history stage choice .stop = .execute handle tool) :
    (handle, tool) ∈ historyCommitments history ∧ handle.stage = stage ∧
      (historyExecutions history).any (fun pair => pair.1.stage == stage) = false := by
  unfold Parameters.repairAction at selected
  split at selected
  · cases selected
  · rename_i notExecuted
    have hfalse : (historyExecutions history).any (fun pair => pair.1.stage == stage) = false :=
      Bool.eq_false_iff.mpr notExecuted
    cases hfind : (historyCommitments history).find? (fun pair => pair.1.stage == stage) with
    | none =>
      simp only [hfind] at selected
      cases hvisible : referenceVisibleHandle history stage <;> cases hchoice : choice <;>
        simp only [hvisible, hchoice] at selected <;> cases selected
    | some pair =>
      simp only [hfind, Action.execute.injEq] at selected
      obtain ⟨hhandle, htool⟩ := selected
      have hpair : pair = (handle, tool) := Prod.ext hhandle htool
      subst pair
      refine ⟨List.mem_of_find?_eq_some hfind, ?_, hfalse⟩
      have found := List.find?_some hfind
      exact beq_iff_eq.mp found

theorem retained_rule_at_barrier (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ) {Seed : Type*}
    (seed : Seed) (history : List (VisibleEvent (starInstance P.tools order)))
    (active : historyHalted history = false)
    (terminal : historyCursor history = (starInstance P.tools order).stageCount) :
    P.starReferenceRule order kind r limit seed history = P.barrierAction order history := by
  cases kind with
  | current => exact (retained rfl).elim
  | earlyRetained | lateRetained => simp only [Parameters.starReferenceRule, Parameters.candidateWithTesting,
      active, Bool.false_eq_true, ↓reduceIte, terminal, lt_self_iff_false, ↓reduceDIte]

theorem barrierAction_allocate_selection (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.barrierAction order history = .allocate handle tool) :
    ∃ stage, (Finset.univ.filter fun i => reportedError history i).card ≤ P.tools ∧
      reportedError history stage = true ∧ referenceVisibleHandle history stage = some handle ∧
      P.retainedToolChoice order history stage = some tool ∧
      (historyCommitments history).find? (fun pair => pair.1.stage == stage) = none ∧
      (historyExecutions history).any (fun pair => pair.1.stage == stage) = false ∧ handle.stage = stage := by
  classical
  unfold Parameters.barrierAction at selected
  dsimp only at selected
  split at selected
  · cases selected
  · rename_i hsize
    cases hfirst : firstOfFinset ((Finset.univ.filter fun i => reportedError history i).filter
        fun i => !(historyExecutions history).any (fun pair => pair.1.stage == i)) with
    | none => simp only [hfirst] at selected; cases selected
    | some stage =>
      simp only [hfirst] at selected
      have member := firstOfFinset_mem _ stage hfirst
      have wrong := (Finset.mem_filter.mp (Finset.mem_filter.mp member).1).2
      obtain ⟨visible, chosen, uncommitted, unexecuted, hstage⟩ :=
        repairAction_allocate_selection P order history stage _ handle tool selected
      exact ⟨stage, Nat.le_of_not_gt hsize, wrong, visible, chosen, uncommitted, unexecuted, hstage⟩

theorem barrierAction_execute_selection (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (handle : MismatchHandle (starInstance P.tools order)) (tool : (starInstance P.tools order).Tool)
    (selected : P.barrierAction order history = .execute handle tool) :
    ∃ stage, (Finset.univ.filter fun i => reportedError history i).card ≤ P.tools ∧
      reportedError history stage = true ∧ (handle, tool) ∈ historyCommitments history ∧
      handle.stage = stage ∧
      (historyExecutions history).any (fun pair => pair.1.stage == stage) = false := by
  classical
  unfold Parameters.barrierAction at selected
  dsimp only at selected
  split at selected
  · cases selected
  · rename_i hsize
    cases hfirst : firstOfFinset ((Finset.univ.filter fun i => reportedError history i).filter
        fun i => !(historyExecutions history).any (fun pair => pair.1.stage == i)) with
    | none => simp only [hfirst] at selected; cases selected
    | some stage =>
      simp only [hfirst] at selected
      have member := firstOfFinset_mem _ stage hfirst
      have wrong := (Finset.mem_filter.mp (Finset.mem_filter.mp member).1).2
      obtain ⟨committed, hstage, unexecuted⟩ :=
        repairAction_execute_selection P order history stage _ handle tool selected
      exact ⟨stage, Nat.le_of_not_gt hsize, wrong, committed, hstage, unexecuted⟩

theorem repairAction_cases (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage)
    (choice : Option (starInstance P.tools order).Tool) :
    P.repairAction order history stage choice .stop = .stop ∨
      P.repairAction order history stage choice .stop = .abandon ∨
      (∃ handle tool, P.repairAction order history stage choice .stop = .allocate handle tool) ∨
      (∃ handle tool, P.repairAction order history stage choice .stop = .execute handle tool) := by
  unfold Parameters.repairAction
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem barrierAction_cases (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) :
    P.barrierAction order history = .stop ∨ P.barrierAction order history = .abandon ∨
      (∃ handle tool, P.barrierAction order history = .allocate handle tool) ∨
      (∃ handle tool, P.barrierAction order history = .execute handle tool) := by
  classical
  unfold Parameters.barrierAction
  dsimp only
  split
  · simp
  · split
    · simp
    · exact repairAction_cases P order history _ _

end PStarLR
