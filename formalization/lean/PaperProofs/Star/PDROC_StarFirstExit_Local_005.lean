module

public import PaperProofs.Star.PDROC_StarFirstExit_Local_004
public import PaperProofs.Star.PDROC_StarLRHead_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarFirstExit.Local

/-- Same-stage active/open endpoints exclude a write, advance or halt.
Every remaining genuine event preserves the original computed selector. -/
theorem chosenTarget_step_same_open (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) (tapes : ReviewTapes (P.input order))
    {s next : State (starInstance P.tools order)} {action : Action (starInstance P.tools order)}
    (step : Step (P.input order) C mode accounting tapes s action next)
    (i : (starInstance P.tools order).Stage) (oldLive : liveStage s i) (nextLive : liveStage next i)
    (nextPort : next.ledger.written i = none) :
    P.chosenTargetReal order kind r next.history i = P.chosenTargetReal order kind r s.history i := by
  classical
  cases step with
  | review j live port resources =>
    exact chosenTarget_append_ignored P order kind r s.history
      (.observation j (tapes j (s.ledger.reviews j).toNat).val) (by intro k; rfl) (by intro k; rfl) i
  | write j bit live port resources =>
    have hij : i = j := Fin.ext (oldLive.2.symm.trans live.2)
    subst i
    simp only [record, reportedWriteLedger] at nextPort
    split_ifs at nextPort <;> simp [writeLedger] at nextPort
  | allocate handle tool active valid compatible unused unallocated window resources =>
    exact chosenTarget_append_ignored P order kind r s.history (.committed handle tool)
      (by intro k; rfl) (by intro k; rfl) i
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    exact chosenTarget_append_ignored P order kind r s.history (.executed handle tool)
      (by intro k; rfl) (by intro k; rfl) i
  | advance j live written resources =>
    have hc := nextLive.2
    change s.cursor+1 = i.val at hc
    have ho := oldLive.2
    omega
  | stop active => cases nextLive.1
  | abandon active => cases nextLive.1

theorem chosenTarget_run_succ_same_open (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (clock : ℕ) (i : (starInstance P.tools order).Stage)
    (oldLive : liveStage (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock) i)
    (nextLive : liveStage (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (clock+1)) i)
    (nextPort : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (clock+1)).ledger.written i = none) :
    P.chosenTargetReal order kind r
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (clock+1)).history i =
      P.chosenTargetReal order kind r
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history i := by
  let old := run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock
  have keep := PDROC.StarLocalReview.nextFromFrontier_preserves (P.input order) C .uncapped accounting old
    (P.starReferenceRule order kind r none sample.1 old.history) (frontierOf (P.input order) old sample.2)
    (fun next => liveStage next i → next.ledger.written i = none →
      P.chosenTargetReal order kind r next.history i = P.chosenTargetReal order kind r old.history i)
    (by intro _live _port; rfl)
    (by intro next step live port
        exact chosenTarget_step_same_open P order kind r C .uncapped accounting _ step i oldLive live port)
    (by intro live _port; cases live.1)
  exact keep nextLive nextPort

end PDROC.StarFirstExit.Local
