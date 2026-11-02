module

public import PaperProofs.Paid.PDROC_TruthfulContinuation_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native

namespace PDROC

variable {I : Instance}

theorem reachable_invariant (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) {s next : State I}
    (hp : Relation.ReflTransGen (fun before after => ∃ action,
      Step input C .uncapped accounting tapes before action after) s next)
    (hi : Invariant C s) : Invariant C next := by
  induction hp with
  | refl => exact hi
  | tail _ hs ih => obtain ⟨action, hs⟩ := hs; exact step_invariant input C .uncapped accounting tapes hs ih

theorem reachable_deadlineInvariant (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) {s next : State I}
    (hp : Relation.ReflTransGen (fun before after => ∃ action,
      Step input C .uncapped accounting tapes before action after) s next)
    (hi : DeadlineInvariant C s.ledger s.cursor s.clock) :
    DeadlineInvariant C next.ledger next.cursor next.clock := by
  induction hp with
  | refl => exact hi
  | tail _ hs ih => obtain ⟨action, hs⟩ := hs; exact step_deadlineInvariant input C .uncapped accounting tapes ih hs

theorem reachable_cursorInvariant (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) {s next : State I}
    (hp : Relation.ReflTransGen (fun before after => ∃ action,
      Step input C .uncapped accounting tapes before action after) s next)
    (hi : CursorInvariant s) : CursorInvariant next := by
  induction hp with
  | refl => exact hi
  | tail _ hs ih => obtain ⟨action, hs⟩ := hs; exact step_cursorInvariant input C .uncapped accounting tapes ih hs

theorem reachable_pastPortsWritten (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) {s next : State I}
    (hp : Relation.ReflTransGen (fun before after => ∃ action,
      Step input C .uncapped accounting tapes before action after) s next)
    (hi : PastPortsWritten s) : PastPortsWritten next := by
  induction hp with
  | refl => exact hi
  | tail _ hs ih => obtain ⟨action, hs⟩ := hs; exact step_pastPortsWritten input C .uncapped accounting tapes ih hs

end PDROC
