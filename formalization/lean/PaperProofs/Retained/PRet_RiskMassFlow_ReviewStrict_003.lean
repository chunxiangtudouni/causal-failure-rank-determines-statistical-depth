module

public import PaperProofs.Retained.PRet_RiskMassFlow_Testing_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory

namespace PRetRiskMassFlow

variable {I : Instance}

theorem natCast_succ_le_of_lt (count : ℕ) (stop : ℕ∞) (bound : (count : ℕ∞) < stop) :
    ((count+1 : ℕ) : ℕ∞) ≤ stop := by
  cases stop using ENat.recTopCoe with
  | top => exact le_top
  | coe n => exact ENat.natCast_le_natCast.mpr (Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp bound))

theorem review_stop_strict (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) seed truth tapes n state)
    (active : state.halted = false) (stage : I.Stage) (cursor : state.cursor = stage.val)
    (openPort : state.ledger.written stage = none) (p : ℚ)
    (target : entryTarget I budget stage state.history = some p)
    (selected : retainedRule input budget none seed state.history = .review stage)
    (before : state.ledger.reviews stage ≤ (input.experiment stage).posteriorThresholdStop p (tapes stage)) :
    state.ledger.reviews stage < (input.experiment stage).posteriorThresholdStop p (tapes stage) := by
  obtain ⟨cache,_replay,_healthy,valid,candidate,targetEq⟩ :=
    prefix_open_testing input C hearly accounting budget positive small seed truth tapes path active stage cursor openPort
  have raw := PRetCompletion.rule_raw_of_ne_abandon input budget none seed state.history (.review stage)
    (by intro impossible; cases impossible) selected
  have testing := candidate.symm.trans raw
  obtain ⟨q,chosen,nonhit⟩ := testing_review_nonhit input state.history cache stage valid testing
  have same : q = p := Option.some.inj (chosen.symm.trans (targetEq.symm.trans target))
  subst q
  have alphabet : ∀ symbol ∈ historyObservations state.history stage, symbol < (input.experiment stage).alphabetSize :=
    fun symbol member => prefix_historyObservation_alphabet input C .uncapped accounting
      (retainedRule input budget none) seed truth tapes path stage symbol member
  have falseHit := nonhit alphabet
  have validTarget := entryTarget_valid budget stage state.history p target
  have one : p < 1 := lt_of_le_of_lt validTarget.2 (by norm_num)
  have hitIff := prefix_historyObservationWord_hits_iff input C .uncapped accounting
    (retainedRule input budget none) seed truth tapes path stage alphabet p validTarget.1 one
  apply lt_of_le_of_ne before
  intro eq
  have finite := prefix_reviews_natCast_toNat input C .uncapped accounting
    (retainedRule input budget none) seed truth tapes path stage
  have stopEq : (input.experiment stage).posteriorThresholdStop p (tapes stage) =
      ((state.ledger.reviews stage).toNat : ℕ∞) := eq.symm.trans finite.symm
  have hit := hitIff.mpr ((input.experiment stage).posteriorThresholdStop_hits p (tapes stage) _ stopEq)
  rw [falseHit] at hit
  cases hit

theorem prefix_eq_run_sample (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (sample : Unit × input.World) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n state) :
    run input C .uncapped accounting (retainedRule input budget none) sample n = state := by
  have eq := prefix_eq_run input C .uncapped accounting (retainedRule input budget none) sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) path
  have world : replayWorld input (input.truthAt sample.2) (worldTapes input sample.2) = sample.2 := rfl
  simpa only [world] using eq

theorem entryHistory_at_increment (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (sample : Unit × input.World)
    (n : ℕ) (old next : State I) (stage : I.Stage)
    (oldEq : run input C .uncapped accounting (retainedRule input budget none) sample n = old)
    (nextEq : run input C .uncapped accounting (retainedRule input budget none) sample (n+1) = next)
    (before : old.cursor < stage.val) (cursor : next.cursor = stage.val) :
    entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some next.history := by
  apply (entryHistory_some_iff input C .uncapped accounting (retainedRule input budget none) stage sample next.history).mpr
  refine ⟨n+1,by simpa only [nextEq] using cursor,?_,by rw [nextEq]⟩
  intro k smaller attained
  have mono := run_cursor_monotone input C .uncapped accounting (retainedRule input budget none)
    (retainedRule_uncapped_legal input C hretained accounting budget none) sample (Nat.le_of_lt_succ smaller)
  dsimp only at mono
  rw [oldEq,attained] at mono
  omega

end PRetRiskMassFlow
