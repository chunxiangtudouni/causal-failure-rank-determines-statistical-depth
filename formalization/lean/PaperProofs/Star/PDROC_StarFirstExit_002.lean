module

public import PaperProofs.Star.PDROC_StarFirstExit_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarFirstExit

def NoEarlierHit (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (tapes : ReviewTapes (P.input order)) (s : State (starInstance P.tools order))
    (i : (starInstance P.tools order).Stage) : Prop :=
  match P.chosenTargetReal order kind r s.history i with
  | none => s.ledger.reviews i = 0
  | some target => ∀ k : ℕ, k < (s.ledger.reviews i).toNat →
      |P.channel.experiment.logOddsScore (tapes i) k| < Real.log ((1-target)/target)

def CurrentTestInvariant (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (tapes : ReviewTapes (P.input order)) (s : State (starInstance P.tools order)) : Prop :=
  ∀ i, liveStage s i → s.ledger.written i = none → NoEarlierHit P order kind r tapes s i

theorem noEarlierHit_of_zero (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (tapes : ReviewTapes (P.input order)) (s : State (starInstance P.tools order))
    (i : (starInstance P.tools order).Stage) (zero : s.ledger.reviews i = 0) :
    NoEarlierHit P order kind r tapes s i := by
  unfold NoEarlierHit
  cases P.chosenTargetReal order kind r s.history i <;> simp [zero]

theorem noEarlierHit_transfer (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (tapes : ReviewTapes (P.input order)) (old next : State (starInstance P.tools order))
    (i : (starInstance P.tools order).Stage) (known : NoEarlierHit P order kind r tapes old i)
    (target : P.chosenTargetReal order kind r next.history i = P.chosenTargetReal order kind r old.history i)
    (count : next.ledger.reviews i = old.ledger.reviews i) :
    NoEarlierHit P order kind r tapes next i := by
  unfold NoEarlierHit at known ⊢
  rw [target, count]
  exact known

theorem prefix_currentTestInvariant (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (r : ℝ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order))
    (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {s : State (starInstance P.tools order)}
    (hp : Prefix (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none (Seed := Unit)) () truth tapes n s) :
    CurrentTestInvariant P order kind r tapes s := by
  classical
  induction hp with
  | initial =>
    intro i _live _port
    exact noEarlierHit_of_zero P order kind r tapes _ i rfl
  | @next n s next earlier step ih =>
    generalize selected : P.starReferenceRule order kind r none () s.history = action at step
    cases step with
    | review j live port resources =>
      intro i live' _port'
      have hij : i = j := Fin.ext (live'.2.symm.trans live.2)
      subst i
      have known := ih j live port
      have htarget := chosenTarget_append_ignored P order kind r s.history
        (.observation j (tapes j (s.ledger.reviews j).toNat).val)
        (by intro k; rfl) (by intro k; rfl) j
      have action := (rule_testing_of_live_unwritten P order kind r C accounting truth tapes earlier j live port).symm.trans selected
      rw [testingAction_actual P order kind r C accounting truth tapes earlier j] at action
      unfold NoEarlierHit at known ⊢
      simp only [record, reviewLedger, Function.update_self, htarget]
      cases ht : P.chosenTargetReal order kind r s.history j with
      | none => rw [ht] at action; cases action
      | some target =>
        rw [ht] at known action
        dsimp only at known action
        have nohit : |P.channel.experiment.logOddsScore (tapes j) (s.ledger.reviews j).toNat| <
            Real.log ((1-target)/target) := by
          by_contra absent
          simp only [ite_eq_left (le_of_not_gt absent), reduceCtorEq] at action
        have finite := prefix_reviews_finite (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind r none) () truth tapes earlier j
        have succ : (s.ledger.reviews j + 1).toNat = (s.ledger.reviews j).toNat + 1 := by
          rw [ENat.toNat_add finite (by simp)]
          rfl
        intro k hk
        rw [succ] at hk
        by_cases before : k < (s.ledger.reviews j).toNat
        · exact known k before
        · have eq : k = (s.ledger.reviews j).toNat := by omega
          simpa only [eq] using nohit
    | write j bit live port resources =>
      intro i live' port'
      have hij : i = j := Fin.ext (live'.2.symm.trans live.2)
      subst i
      simp only [record, reportedWriteLedger] at port'
      split_ifs at port' <;> simp [writeLedger] at port'
    | allocate handle tool active valid compatible unused unallocated window resources =>
      intro i live' port'
      apply noEarlierHit_transfer P order kind r tapes s _ i (ih i ⟨active, live'.2⟩ port')
      · exact chosenTarget_append_ignored P order kind r s.history (.committed handle tool)
          (by intro k; rfl) (by intro k; rfl) i
      · rfl
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      intro i live' port'
      apply noEarlierHit_transfer P order kind r tapes s _ i (ih i ⟨active, live'.2⟩ port')
      · exact chosenTarget_append_ignored P order kind r s.history (.executed handle tool)
          (by intro k; rfl) (by intro k; rfl) i
      · rfl
    | advance j live written resources =>
      intro i live' _port'
      have future : s.cursor < i.val := by
        have hc := live'.2
        change s.cursor + 1 = i.val at hc
        omega
      exact noEarlierHit_of_zero P order kind r tapes _ i
        ((prefix_cursorInvariant (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind r none) () truth tapes earlier).future_reviews i future)
    | stop active =>
      intro i live' _port'
      cases live'.1
    | abandon active =>
      intro i live' _port'
      cases live'.1

end PDROC.StarFirstExit
