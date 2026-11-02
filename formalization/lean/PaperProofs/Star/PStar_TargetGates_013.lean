module

public import PaperProofs.Star.PStar_TargetHistory_010
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarTargetGates013

open Common Common.Native Parameters PStarLR PStarTargetHistory010

variable {I : Instance}

theorem prefix_reportedError_iff_wrong (input : StatisticalInput I) (C : Contract I)
    (early : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C mode accounting rule seed truth tapes n state)
    (stage : I.Stage) (written : state.ledger.written stage ≠ none) :
    reportedError state.history stage = true ↔ state.ledger.written stage = some (!state.ledger.truth stage) := by
  obtain ⟨bit, bitWritten⟩ := Option.ne_none_iff_exists'.mp written
  obtain ⟨time, reportTime⟩ := prefix_early_written_reported input C early mode accounting rule
    seed truth tapes path stage written
  unfold reportedError
  rw [prefix_historyWritten input C mode accounting rule seed truth tapes path,
    prefix_historyReport_early input C early mode accounting rule seed truth tapes path,
    bitWritten, reportTime]
  cases bit <;> cases state.ledger.truth stage <;> simp

/-- The original count gate is the true conjunction of all past ordinary
errors at a genuine current-stage prefix. It includes failed paths and uses
actual early reports with their original write serials. -/
theorem prefix_previousAllErrors_iff (input : StatisticalInput I) (C : Contract I)
    (early : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C mode accounting rule seed truth tapes n state)
    (stage : I.Stage) (cursor : state.cursor = stage.val) :
    previousAllErrors state.history stage = true ↔
      ∀ earlier : I.Stage, earlier.val < stage.val →
        state.ledger.written earlier = some (!state.ledger.truth earlier) := by
  rw [previousAllErrors_iff]
  apply forall_congr'
  intro earlier
  apply imp_congr_right
  intro before
  apply prefix_reportedError_iff_wrong input C early mode accounting rule seed truth tapes path earlier
  exact prefix_pastWritten input C mode accounting rule seed truth tapes path earlier (by rwa [cursor])

theorem countChosenTarget_on_prefix (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (countKind : kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst))
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (early : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting (starInstance P.tools order))
    {Seed : Type*} (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool)
    (tapes : ReviewTapes (P.input order)) {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) (stage : (starInstance P.tools order).Stage) (cursor : state.cursor = stage.val) :
    P.chosenTargetReal order kind r state.history stage =
      if (∀ earlier : (starInstance P.tools order).Stage, earlier.val < stage.val →
        state.ledger.written earlier = some (!state.ledger.truth earlier))
      then some (countTargetReal (P.countBudgetReal r stage.val) (P.tools - stage.val)) else none := by
  classical
  have gate := prefix_previousAllErrors_iff (P.input order) C early mode accounting
    (P.starReferenceRule order kind r limit) seed truth tapes path stage cursor
  rcases countKind with rfl | ⟨rfl, rfl⟩
  · cases order <;> simp only [Parameters.chosenTargetReal, gate]
  · simp only [Parameters.chosenTargetReal, gate]

end PaperProofs.Star.PStarTargetGates013
