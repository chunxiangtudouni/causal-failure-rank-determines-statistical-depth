module

public import PaperProofs.Star.PStar_CurrentChoice_001
public import PaperProofs.Star.PStarLR_RepairSelection_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentSelection002

open Common Common.Native Parameters PStarLR

/-- Every real current-script correction comes from the written/reported
current stage. Failed choice branches remain actual abandon actions. -/
theorem current_rule_correction_selection (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) {Seed : Type*} (seed : Seed)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (correcting : IsCorrection (P.starReferenceRule order .current r limit seed history)) :
    ∃ stage : (starInstance P.tools order).Stage,
      historyCursor history = stage.val ∧ reportedError history stage = true ∧
      P.starReferenceRule order .current r limit seed history =
        P.repairAction order history stage (P.currentToolChoice order history stage) (.advance stage) := by
  classical
  unfold Parameters.starReferenceRule Parameters.candidateWithTesting at correcting
  split at correcting
  · exact False.elim correcting
  · rename_i active
    split at correcting
    · rename_i cursor
      dsimp only at correcting
      split at correcting
      · exact (testingActionReal_not_correction P order .current r limit history _ correcting).elim
      · rename_i bit written
        split at correcting
        · exact False.elim correcting
        · rename_i pair reported
          split at correcting
          · rename_i wrong
            refine ⟨⟨historyCursor history, cursor⟩, rfl, wrong, ?_⟩
            simp only [Parameters.starReferenceRule, Parameters.candidateWithTesting, active, Bool.false_eq_true, ↓reduceIte,
              cursor, ↓reduceDIte, written, reported, wrong]
          · exact False.elim correcting
    · split at correcting <;> exact False.elim correcting

/-- Actual current-window allocation selection, preserving the genuine
visible handle, chosen tool and both original unallocated/unused-stage tests. -/
theorem repairAction_allocate_advance_selection (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage)
    (choice : Option (starInstance P.tools order).Tool) (handle : MismatchHandle (starInstance P.tools order))
    (tool : (starInstance P.tools order).Tool)
    (selected : P.repairAction order history stage choice (.advance stage) = .allocate handle tool) :
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

/-- Actual current-window execute selection uses a real commitment and a
not-yet-executed stage; it does not assume a successful final matching. -/
theorem repairAction_execute_advance_selection (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage)
    (choice : Option (starInstance P.tools order).Tool) (handle : MismatchHandle (starInstance P.tools order))
    (tool : (starInstance P.tools order).Tool)
    (selected : P.repairAction order history stage choice (.advance stage) = .execute handle tool) :
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

end PaperProofs.Star.PStarCurrentSelection002
