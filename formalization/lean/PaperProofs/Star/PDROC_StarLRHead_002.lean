module

public import PaperProofs.Star.PDROC_StarLRHead_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarLRHead

theorem reference_head_hit (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (tape : P.channel.experiment.Tape) (n : ℕ)
    (stop : realPosteriorStop P.channel.experiment r tape = n) :
    Real.log ((1-r)/r) ≤ |P.channel.experiment.logOddsScore tape n| := by
  have exit := headExitStop_hits (P.input order) (firstStage P.tools order)
    (P.starReferenceRule order .lateRetained r none (Seed := Unit)) () tape n
    ((reference_head_stop P order r tape).trans stop)
  rw [reference_head_action] at exit
  by_contra absent
  simp only [ite_eq_right absent, ne_eq, not_true_eq_false] at exit

theorem reference_head_write (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (tape : P.channel.experiment.Tape) (n : ℕ)
    (stop : realPosteriorStop P.channel.experiment r tape = n) :
    P.starReferenceRule order .lateRetained r none (Seed := Unit) ()
      (headReviewHistory (P.input order) (firstStage P.tools order) tape n) =
      .write (firstStage P.tools order)
        ((P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)).rule.decision () tape) := by
  rw [reference_head_action, ite_eq_left (reference_head_hit P order r tape n stop)]
  rw [PStarLR.realTarget_test_decision P.channel r tape n stop]

theorem reference_head_decision (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (tape : P.channel.experiment.Tape) (n : ℕ)
    (stop : realPosteriorStop P.channel.experiment r tape = n) :
    headExitDecision (P.input order) (firstStage P.tools order)
      (P.starReferenceRule order .lateRetained r none (Seed := Unit)) () tape =
      (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)).rule.decision () tape := by
  exact headExitDecision_of_write (P.input order) (firstStage P.tools order)
    (P.starReferenceRule order .lateRetained r none) () tape n _
    ((reference_head_stop P order r tape).trans stop) (reference_head_write P order r tape n stop)

theorem reference_run_write_at_stop (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (n : ℕ)
    (stop : realPosteriorStop P.channel.experiment r
      ((P.input order).reviewAt sample.2 (firstStage P.tools order)) = n) :
    let stage := firstStage P.tools order
    let tape := (P.input order).reviewAt sample.2 stage
    let state := headReviewState (P.input order) accounting stage ((P.input order).truthAt sample.2) tape n
    let bit := (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)).rule.decision () tape
    run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none) sample (n+1) =
      record accounting state (.write stage bit) (writeResponses C state stage bit)
        (reportedWriteLedger C state stage bit) 0 false := by
  dsimp only
  let stage := firstStage P.tools order
  let tape := (P.input order).reviewAt sample.2 stage
  let state := headReviewState (P.input order) accounting stage ((P.input order).truthAt sample.2) tape n
  let bit := (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)).rule.decision () tape
  have before := reference_run_before_stop P order r C accounting sample n (by rw [stop])
  have active : state.halted = false := headReviewState_active (P.input order) accounting stage _ tape n
  have cursor : state.cursor = 0 := headReviewState_cursor (P.input order) accounting stage _ tape n
  have live : liveStage state stage := ⟨active, cursor⟩
  have port : state.ledger.written stage = none :=
    congrFun (headReviewState_written (P.input order) accounting stage _ tape n) stage
  have next := Step.write (input := P.input order) (C := C) (mode := .uncapped)
    (accounting := accounting) (tapes := worldTapes (P.input order) sample.2) state stage bit
    live port (Or.inl rfl)
  rw [cursor] at next
  apply run_succ_of_step
  · rw [before]
    exact active
  · rw [before, headReviewState_history]
    cases sample.1
    rw [reference_head_write P order r tape n stop]
    exact next

theorem reference_head_charge_world_law (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ) :
    (∫⁻ sample : Unit × (P.input order).World,
      P.channel.experiment.observationCharge
        (realPosteriorStop P.channel.experiment r
          ((P.input order).reviewAt sample.2 (firstStage P.tools order)))
        ∂(P.input order).seededWorldLaw (Measure.dirac ())) =
      P.channel.experiment.bayesObservationCharge (Measure.dirac ())
        (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)) := by
  have law := bayesObservationCharge_eq_seededWorld_integral (P.input order)
    (firstStage P.tools order) (Measure.dirac ())
    (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r))
  refine Eq.trans ?_ law.symm
  apply lintegral_congr
  intro sample
  congr 1
  cases sample.1
  exact PStarLR.realPosteriorStop_eq_hitting P.channel r _

end PDROC.StarLRHead
