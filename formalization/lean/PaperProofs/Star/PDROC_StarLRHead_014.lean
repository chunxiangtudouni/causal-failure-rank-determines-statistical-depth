module

public import PaperProofs.Star.PDROC_StarLRHead_013
public import PaperProofs.Common.NativeCausality

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native

namespace PDROC.StarLocalReview

variable {I : Instance}

theorem nextFromFrontier_cursor_bounds (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (state : State I)
    (action : Action I) (frontier : Frontier input) :
    state.cursor ≤ (nextFromFrontier input C mode accounting state action frontier).cursor ∧
      (nextFromFrontier input C mode accounting state action frontier).cursor ≤ state.cursor+1 := by
  apply nextFromFrontier_preserves input C mode accounting state action frontier
    (fun next => state.cursor ≤ next.cursor ∧ next.cursor ≤ state.cursor+1)
  · exact ⟨le_rfl, Nat.le_succ _⟩
  · intro next step
    exact step_cursor_bounds input C mode accounting _ step
  · exact ⟨le_rfl, Nat.le_succ _⟩

theorem run_cursor_mono_no_legal {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) :
    Monotone (fun n => (run input C mode accounting rule sample n).cursor) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (nextFromFrontier_cursor_bounds input C mode accounting _ _ _).1

theorem run_active_of_le_no_legal {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) {earlier later : ℕ} (order : earlier ≤ later)
    (active : (run input C mode accounting rule sample later).halted = false) :
    (run input C mode accounting rule sample earlier).halted = false := by
  by_contra absent
  have halted : (run input C mode accounting rule sample earlier).halted = true :=
    Bool.eq_true_of_not_eq_false absent
  obtain ⟨extra, equal⟩ := Nat.exists_eq_add_of_le order
  have absorb := run_after_halt input C mode accounting rule sample earlier halted extra
  rw [← equal] at absorb
  rw [absorb, halted] at active
  cases active

theorem run_unwritten_of_le_no_legal {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) {earlier later : ℕ} (order : earlier ≤ later)
    (stage : I.Stage) (unwritten : (run input C mode accounting rule sample later).ledger.written stage = none) :
    (run input C mode accounting rule sample earlier).ledger.written stage = none := by
  by_contra absent
  obtain ⟨bit, written⟩ := Option.ne_none_iff_exists'.mp absent
  obtain ⟨extra, equal⟩ := Nat.exists_eq_add_of_le order
  have preserve := run_written_after_no_legal input C mode accounting rule sample earlier extra stage bit written
  rw [← equal, unwritten] at preserve
  cases preserve

theorem run_cursor_eq_between_no_legal {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) {start middle finish : ℕ}
    (lower : start ≤ middle) (upper : middle ≤ finish)
    (equalEnds : (run input C mode accounting rule sample start).cursor =
      (run input C mode accounting rule sample finish).cursor) :
    (run input C mode accounting rule sample middle).cursor =
      (run input C mode accounting rule sample start).cursor := by
  have mono := run_cursor_mono_no_legal input C mode accounting rule sample
  exact Nat.le_antisymm ((mono upper).trans_eq equalEnds.symm) (mono lower)

theorem run_live_unwritten_between_no_legal {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (sample : Seed × input.World) (start middle finish : ℕ)
    (lower : start ≤ middle) (upper : middle ≤ finish) (stage : I.Stage)
    (cursorStart : (run input C mode accounting rule sample start).cursor = stage.val)
    (liveFinish : liveStage (run input C mode accounting rule sample finish) stage)
    (unwrittenFinish : (run input C mode accounting rule sample finish).ledger.written stage = none) :
    liveStage (run input C mode accounting rule sample middle) stage ∧
      (run input C mode accounting rule sample middle).ledger.written stage = none := by
  have equalEnds := cursorStart.trans liveFinish.2.symm
  have cursorMiddle := run_cursor_eq_between_no_legal input C mode accounting rule sample lower upper equalEnds
  exact ⟨⟨run_active_of_le_no_legal input C mode accounting rule sample upper liveFinish.1,
    cursorMiddle.trans cursorStart⟩,
    run_unwritten_of_le_no_legal input C mode accounting rule sample upper stage unwrittenFinish⟩

end PDROC.StarLocalReview
