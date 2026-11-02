module

public import PaperProofs.Retained.PRet_Alignment_Actual_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics

namespace PRetCompletion

variable {I : Instance}

theorem visible_stage (history : List (VisibleEvent I)) (stage : I.Stage) (handle : MismatchHandle I)
    (visible : referenceVisibleHandle history stage = some handle) : handle.stage = stage := by
  unfold referenceVisibleHandle at visible
  cases write : historyWrite history stage with
  | none => rw [write] at visible; cases visible
  | some pair =>
    rw [write] at visible
    have eq : (⟨stage,pair.2⟩ : MismatchHandle I) = handle := Option.some.inj visible
    exact (congrArg MismatchHandle.stage eq).symm

def pending (I : Instance) (history : List (VisibleEvent I)) : Option I.Stage :=
  (List.finRange I.stageCount).find? (fun stage => decide (stage ∈ reportedErrors I history I.stageCount) &&
    !((historyExecutions history).any (fun e => e.1.stage == stage)))

set_option backward.isDefEq.respectTransparency.types false in
theorem terminal_allocate_selection (history : List (VisibleEvent I)) (handle : MismatchHandle I) (tool : I.Tool)
    (selected : terminalMatchingAction I history = .allocate handle tool) :
    ∃ assignment stage, firstAssignment I (reportedErrors I history I.stageCount) = some assignment ∧
      pending I history = some stage ∧ assignment[stage.val]?.join = some tool ∧
      referenceVisibleHandle history stage = some handle ∧
      (historyCommitments history).find? (fun a => a.1.stage == stage) = none ∧ handle.stage = stage := by
  unfold terminalMatchingAction at selected
  dsimp only at selected
  cases first : firstAssignment I (reportedErrors I history I.stageCount) with
  | none => rw [first] at selected; cases selected
  | some assignment =>
    rw [first] at selected
    change (match pending I history with | none => Action.stop | some stage => _) = Action.allocate handle tool at selected
    cases find : pending I history with
    | none => rw [find] at selected; cases selected
    | some stage =>
      rw [find] at selected
      dsimp only at selected
      cases slot : assignment[stage.val]?.join with
      | none => rw [slot] at selected; cases visible : referenceVisibleHandle history stage <;> rw [visible] at selected <;> cases selected
      | some chosen =>
        rw [slot] at selected
        cases visible : referenceVisibleHandle history stage with
        | none => rw [visible] at selected; cases selected
        | some actual =>
          rw [visible] at selected
          dsimp only at selected
          cases old : (historyCommitments history).find? (fun a => a.1.stage == stage) with
          | some pair =>
            rw [old] at selected
            dsimp only at selected
            split_ifs at selected
          | none =>
            rw [old] at selected
            have eq := Action.allocate.inj selected
            obtain ⟨rfl,rfl⟩ := eq
            refine ⟨assignment,stage,?_,?_,?_,?_,?_,visible_stage history stage actual visible⟩
            · rfl
            · rfl
            · exact slot
            · exact visible
            · exact old

theorem candidate_at_terminal (input : StatisticalInput I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) (active : historyHalted history = false)
    (cursor : historyCursor history = I.stageCount) :
    retainedCandidate input budget limit history = terminalMatchingAction I history := by
  simp only [retainedCandidate,active,Bool.false_eq_true,↓reduceIte,cursor,lt_self_iff_false,dite_false]

theorem rule_raw_of_ne_abandon (input : StatisticalInput I) (budget : ℚ) (limit : ReferenceObservationLimit I)
    (seed : Unit) (history : List (VisibleEvent I)) (action : Action I) (notAbandon : action ≠ .abandon)
    (selected : retainedRule input budget limit seed history = action) :
    retainedCandidate input budget limit history = action := by
  unfold retainedRule PRetRetainedGuard007.guarded at selected
  split at selected
  · exact selected
  · exact (notAbandon selected.symm).elim

end PRetCompletion
