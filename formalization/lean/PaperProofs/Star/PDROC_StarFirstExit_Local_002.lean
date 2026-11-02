module

public import PaperProofs.Star.PDROC_StarFirstExit_Local_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarFirstExit.Local

structure ReviewFrame {I : Instance} (s : State I) (i : I.Stage) (count : ℕ) : Prop where
  live : liveStage s i
  unwritten : s.ledger.written i = none
  reviews : s.ledger.reviews i = count

theorem selected_review_of_frame (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (clock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (count : ℕ)
    (frame : ReviewFrame (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock) i count)
    (targetEq : P.chosenTargetReal order kind r
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history i = some target)
    (before : (count : ℕ∞) < realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i)) :
    P.starReferenceRule order kind r none sample.1
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history = .review i := by
  have action := actual_action P order kind r C accounting sample clock i frame.live frame.unwritten
  rw [targetEq] at action
  have nohit := realStop_before P.channel.experiment target ((P.input order).reviewAt sample.2 i) count before
  simpa only [frame.reviews, ENat.toNat_natCast, ite_eq_right (not_le_of_gt nohit)] using action

theorem reviewPrefix (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (stable : StableTarget P order kind r C accounting sample entryClock i target)
    (k : ℕ) (before : (k : ℕ∞) ≤ realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i)) :
    ReviewFrame (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (entryClock+k)) i k := by
  induction k with
  | zero => exact ⟨entry.live, entry.unwritten, entry.reviews_zero⟩
  | succ k ih =>
    have hk : (k : ℕ∞) ≤ realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) :=
      (show (k : ℕ∞) ≤ (k+1 : ℕ) from by exact_mod_cast Nat.le_succ k).trans before
    have known := ih hk
    have hklt : (k : ℕ∞) < realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) :=
      (show (k : ℕ∞) < (k+1 : ℕ) from by exact_mod_cast Nat.lt_succ_self k).trans_le before
    have selected := selected_review_of_frame P order kind r C accounting sample (entryClock+k) i target k known
      (stable k known.live known.unwritten) hklt
    have step := Step.review (input := P.input order) (C := C) (mode := .uncapped)
      (accounting := accounting) (tapes := worldTapes (P.input order) sample.2)
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (entryClock+k)) i
      known.live known.unwritten (Or.inl rfl)
    have next := run_succ_of_step (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample (entryClock+k) _ known.live.1
      (by rw [selected]; exact step)
    rw [show entryClock+(k+1) = entryClock+k+1 by omega, next]
    refine ⟨⟨rfl, known.live.2⟩, known.unwritten, ?_⟩
    simp only [record, reviewLedger, Function.update_self, known.reviews, Nat.cast_add, Nat.cast_one]

theorem review_action (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (stable : StableTarget P order kind r C accounting sample entryClock i target)
    (k : ℕ) (before : (k : ℕ∞) < realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i)) :
    P.starReferenceRule order kind r none sample.1
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (entryClock+k)).history = .review i := by
  have frame := reviewPrefix P order kind r C accounting sample entryClock i target entry stable k before.le
  exact selected_review_of_frame P order kind r C accounting sample (entryClock+k) i target k frame
    (stable k frame.live frame.unwritten) before

theorem write_action (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (stable : StableTarget P order kind r C accounting sample entryClock i target)
    (k : ℕ) (stop : realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) = k) :
    P.starReferenceRule order kind r none sample.1
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (entryClock+k)).history =
        .write i (decide (0 ≤ P.channel.experiment.logOddsScore ((P.input order).reviewAt sample.2 i) k)) := by
  have frame := reviewPrefix P order kind r C accounting sample entryClock i target entry stable k (by rw [stop])
  have action := actual_action P order kind r C accounting sample (entryClock+k) i frame.live frame.unwritten
  rw [stable k frame.live frame.unwritten] at action
  have hit := realStop_hits P.channel.experiment target ((P.input order).reviewAt sample.2 i) k stop
  simpa only [frame.reviews, ENat.toNat_natCast, ite_eq_left hit] using action

theorem firstWrite_packet (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (stable : StableTarget P order kind r C accounting sample entryClock i target)
    (k : ℕ) (stop : realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) = k) :
    let s := run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (entryClock+k)
    let bit := decide (0 ≤ P.channel.experiment.logOddsScore ((P.input order).reviewAt sample.2 i) k)
    run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (entryClock+k+1) =
      record accounting s (.write i bit) (writeResponses C s i bit) (reportedWriteLedger C s i bit) s.cursor false := by
  dsimp only
  have frame := reviewPrefix P order kind r C accounting sample entryClock i target entry stable k (by rw [stop])
  have selected := write_action P order kind r C accounting sample entryClock i target entry stable k stop
  have step := Step.write (input := P.input order) (C := C) (mode := .uncapped)
    (accounting := accounting) (tapes := worldTapes (P.input order) sample.2)
    (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (entryClock+k)) i
    (decide (0 ≤ P.channel.experiment.logOddsScore ((P.input order).reviewAt sample.2 i) k)) frame.live frame.unwritten (Or.inl rfl)
  exact run_succ_of_step (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) sample (entryClock+k) _ frame.live.1
    (by rw [selected]; exact step)

theorem firstWrite_frame (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (stable : StableTarget P order kind r C accounting sample entryClock i target)
    (k : ℕ) (stop : realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) = k) :
    let after := run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (entryClock+k+1)
    after.ledger.written i = some (decide (0 ≤ P.channel.experiment.logOddsScore ((P.input order).reviewAt sample.2 i) k)) ∧
      after.ledger.reviews i = k ∧ after.cursor = i.val ∧ after.halted = false := by
  dsimp only
  have frame := reviewPrefix P order kind r C accounting sample entryClock i target entry stable k (by rw [stop])
  rw [firstWrite_packet P order kind r C accounting sample entryClock i target entry stable k stop]
  constructor
  · classical
    simp only [record, reportedWriteLedger]
    split_ifs <;> simp only [writeLedger, Function.update_self]
  constructor
  · classical
    simp only [record, reportedWriteLedger]
    split_ifs <;> exact frame.reviews
  exact ⟨frame.live.2, rfl⟩

theorem infinite_reviewPrefix (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (stable : StableTarget P order kind r C accounting sample entryClock i target)
    (infinite : realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) = ⊤) (k : ℕ) :
    ReviewFrame (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (entryClock+k)) i k :=
  reviewPrefix P order kind r C accounting sample entryClock i target entry stable k (by rw [infinite]; exact le_top)

end PDROC.StarFirstExit.Local
