module

public import PaperProofs.Star.PStarLR_ChoiceExists_009
public import PaperProofs.Star.PStarLR_RepairSelection_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

namespace PStarLR

theorem repairAction_stop_is_executed (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage)
    (choice : Option (starInstance P.tools order).Tool)
    (selected : P.repairAction order history stage choice .stop = .stop) :
    (historyExecutions history).any (fun pair => pair.1.stage == stage) = true := by
  unfold Parameters.repairAction at selected
  split at selected
  · assumption
  · cases hfind : (historyCommitments history).find? (fun pair => pair.1.stage == stage) with
    | some pair => simp only [hfind] at selected; cases selected
    | none =>
      simp only [hfind] at selected
      cases hvisible : referenceVisibleHandle history stage <;> cases hchoice : choice <;>
        simp only [hvisible, hchoice] at selected <;> cases selected

theorem barrierAction_ne_abandon_of_good (P : PaperProofs.Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (policy : PolicyRule (starInstance P.tools order) Seed) (seed : Seed)
    (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting policy seed truth tapes n state)
    (complete : allWritten state.ledger)
    (size : (PaperProofs.Retained.ordinaryMismatches state.ledger).card ≤ P.tools) :
    P.barrierAction order state.history ≠ .abandon := by
  classical
  have small : (Finset.univ.filter fun i => reportedError state.history i).card ≤ P.tools := by
    rw [prefix_complete_errors (P.input order) C mode accounting policy seed truth tapes path complete]
    exact size
  unfold Parameters.barrierAction
  dsimp only
  rw [ite_eq_right (Nat.not_lt.mpr small)]
  cases hfirst : firstOfFinset ((Finset.univ.filter fun i => reportedError state.history i).filter
      fun i => !(historyExecutions state.history).any (fun pair => pair.1.stage == i)) with
  | none => simp
  | some stage =>
    dsimp only
    have member := firstOfFinset_mem _ stage hfirst
    have wrong := (Finset.mem_filter.mp (Finset.mem_filter.mp member).1).2
    have pending := (Finset.mem_filter.mp member).2
    have notExecuted : (historyExecutions state.history).any (fun pair => pair.1.stage == stage) = false := by
      cases hx : (historyExecutions state.history).any (fun pair => pair.1.stage == stage) <;> simp_all
    unfold Parameters.repairAction
    rw [notExecuted]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hfind : (historyCommitments state.history).find? (fun pair => pair.1.stage == stage) with
    | some pair => simp
    | none =>
      have valid := prefix_reportedError_genuine (P.input order) C mode accounting policy seed truth tapes path stage wrong
      have visible := prefix_referenceVisibleHandle_valid (P.input order) C mode accounting policy seed truth tapes path _ valid
      obtain ⟨tool, chosen⟩ := retainedToolChoice_exists_at_barrier P order C mode accounting policy seed truth tapes
        path complete size stage wrong
      rw [visible, chosen]
      simp

theorem barrierAction_stop_covers_mismatches (P : PaperProofs.Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (policy : PolicyRule (starInstance P.tools order) Seed) (seed : Seed)
    (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting policy seed truth tapes n state)
    (complete : allWritten state.ledger) (selected : P.barrierAction order state.history = .stop) :
    PaperProofs.Retained.ordinaryMismatches state.ledger ⊆ PaperProofs.Retained.executedStages state.ledger := by
  classical
  unfold Parameters.barrierAction at selected
  dsimp only at selected
  split at selected
  · cases selected
  · cases hfirst : firstOfFinset ((Finset.univ.filter fun i => reportedError state.history i).filter
        fun i => !(historyExecutions state.history).any (fun pair => pair.1.stage == i)) with
    | some stage =>
      simp only [hfirst] at selected
      have executed := repairAction_stop_is_executed P order state.history stage _ selected
      have pending := (Finset.mem_filter.mp (firstOfFinset_mem _ stage hfirst)).2
      simp only [executed, Bool.not_true, Bool.false_eq_true] at pending
    | none =>
      have empty : ((Finset.univ.filter fun i => reportedError state.history i).filter
          fun i => !(historyExecutions state.history).any (fun pair => pair.1.stage == i)) = ∅ := by
        unfold firstOfFinset at hfirst
        split_ifs at hfirst with nonempty
        exact Finset.not_nonempty_iff_eq_empty.mp nonempty
      intro stage wrong
      have reportedWrong := (prefix_complete_reportedError (P.input order) C mode accounting policy seed truth tapes
        path complete stage).mpr wrong
      by_contra noExecution
      have anyFalse : (historyExecutions state.history).any (fun pair => pair.1.stage == stage) = false := by
        apply List.any_eq_false.mpr
        intro pair member unequal
        rw [prefix_historyExecutions (P.input order) C mode accounting policy seed truth tapes path] at member
        obtain ⟨execution, executed, rfl⟩ := List.mem_map.mp member
        apply noExecution
        exact (PaperProofs.Retained.mem_executedStages state.ledger stage).mpr
          ⟨execution, executed, beq_iff_eq.mp unequal⟩
      have pending : stage ∈ ((Finset.univ.filter fun i => reportedError state.history i).filter
          fun i => !(historyExecutions state.history).any (fun pair => pair.1.stage == i)) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ stage, reportedWrong⟩,
          by rw [anyFalse]; rfl⟩
      rw [empty] at pending
      cases pending

end PStarLR
