module

public import PaperProofs.Star.PDROC_StarFirstExit_Local_002
public import PaperProofs.Star.PDROC_StarLRHead_013
public import Mathlib.Algebra.Order.Floor.Extended

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarFirstExit.Local

/-- All-clock actual stage counts, including finite entry clock, first write,
permanent closed port and infinite nonreturn. The existing ledger is retained. -/
theorem runReviews_eq_realStop (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (stable : StableTarget P order kind r C accounting sample entryClock i target) :
    (⨆ clock : ℕ, (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample clock).ledger.reviews i) =
        realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) := by
  by_cases infinite : realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) = ⊤
  · rw [infinite]
    apply top_unique
    rw [← ENat.iSup_natCast]
    apply iSup_le
    intro k
    have frame := infinite_reviewPrefix P order kind r C accounting sample entryClock i target entry stable infinite k
    calc
      (k : ℕ∞) = (run (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind r none) sample (entryClock+k)).ledger.reviews i := frame.reviews.symm
      _ ≤ _ := le_iSup (fun clock : ℕ => (run (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind r none) sample clock).ledger.reviews i) (entryClock+k)
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp infinite
    rw [← hk]
    have frame := firstWrite_frame P order kind r C accounting sample entryClock i target entry stable k hk.symm
    have mono := PDROC.StarLocalReview.run_reviews_mono_no_legal (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none) sample i
    apply le_antisymm
    · apply iSup_le
      intro clock
      by_cases earlier : clock ≤ entryClock+k+1
      · exact (mono earlier).trans_eq frame.2.1
      · have later : entryClock+k+1 ≤ clock := by omega
        have count := PDROC.StarLocalReview.run_reviews_written_port_no_legal (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind r none) sample (entryClock+k+1) (clock-(entryClock+k+1)) i
          (decide (0 ≤ P.channel.experiment.logOddsScore ((P.input order).reviewAt sample.2 i) k)) frame.1
        rw [Nat.add_sub_of_le later] at count
        exact (count.trans frame.2.1).le
    · calc
        (k : ℕ∞) = (run (P.input order) C .uncapped accounting
            (P.starReferenceRule order kind r none) sample (entryClock+k+1)).ledger.reviews i := frame.2.1.symm
        _ ≤ _ := le_iSup (fun clock : ℕ => (run (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind r none) sample clock).ledger.reviews i) (entryClock+k+1)

/-- Actual paid observations on this stage, including infinity, with the
original runStageObservationBill and original observationCharge. -/
theorem runStageObservationBill_eq (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) (entry : Entry P order kind r C accounting sample entryClock i)
    (stable : StableTarget P order kind r C accounting sample entryClock i target) :
    runStageObservationBill (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) i sample =
      P.channel.experiment.observationCharge
        (realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i)) := by
  unfold runStageObservationBill
  rw [← ENNReal.mul_iSup, ← ENat.toENNReal_iSup,
    runReviews_eq_realStop P order kind r C accounting sample entryClock i target entry stable]
  rw [P.channel.experiment.observationCharge_eq]
  have samples (n : ℕ∞) : PaperProofs.Statistics.BinaryExperiment.sampleCountENNReal n = (n : ℝ≥0∞) := by
    cases n using ENat.recTopCoe <;> simp [PaperProofs.Statistics.BinaryExperiment.sampleCountENNReal]
  rw [samples]
  rfl

end PDROC.StarFirstExit.Local
