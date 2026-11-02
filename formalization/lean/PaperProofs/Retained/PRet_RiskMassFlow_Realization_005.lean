module

public import PaperProofs.Retained.PRet_RiskMassFlow_Origin_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory

namespace PRetRiskMassFlow

variable {I : Instance}

theorem prefix_review_realization (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (sample : Unit × input.World) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n state)
    (active : state.halted = false) (stage : I.Stage)
    (selected : retainedRule input budget none sample.1 state.history = .review stage) :
    ∃ history p, entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some history ∧
      entryTarget I budget stage history = some p ∧
      state.ledger.reviews stage < (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 := by
  obtain ⟨next,step⟩ := retainedRule_uncapped_legal input C hretained accounting budget none sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) n state path active
  rw [selected] at step
  cases step with
  | review stage live port resources =>
    obtain ⟨history,entry,replayEq,progress⟩ :=
      prefix_testing_origin input C hretained accounting budget positive small sample path active stage live.2
    obtain ⟨cache,_replay,_healthy,valid,candidate,targetEq⟩ :=
      prefix_open_testing input C hretained.1 accounting budget positive small sample.1 (input.truthAt sample.2)
        (worldTapes input sample.2) path active stage live.2 port
    have raw := PRetCompletion.rule_raw_of_ne_abandon input budget none sample.1 state.history (.review stage)
      (by intro impossible; cases impossible) selected
    obtain ⟨p,target,_nonhit⟩ := testing_review_nonhit input state.history cache stage valid (candidate.symm.trans raw)
    have currentTarget := targetEq.trans target
    have strict := review_stop_strict input C hretained.1 accounting budget positive small sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) path active stage live.2 port p currentTarget selected
      (progress port p currentTarget)
    have worldTape : worldTapes input sample.2 stage = (sample.2 stage).2 := by funext k; rfl
    exact ⟨history,p,entry,(entryTarget_congr budget stage _ _ replayEq).trans currentTarget,by simpa only [worldTape] using strict⟩

theorem prefix_posteriorWrite_realization (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (sample : Unit × input.World) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n state)
    (active : state.halted = false) (stage : I.Stage) (bit : Bool)
    (selected : retainedRule input budget none sample.1 state.history = .write stage bit)
    (history : List (VisibleEvent I)) (p : ℚ)
    (entry : entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some history)
    (target : entryTarget I budget stage history = some p) :
    (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 = ((state.ledger.reviews stage).toNat : ℕ∞) ∧
      bit = ((input.experiment stage).posteriorSPRT p).rule.decision () (sample.2 stage).2 := by
  obtain ⟨next,step⟩ := retainedRule_uncapped_legal input C hretained accounting budget none sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) n state path active
  rw [selected] at step
  cases step with
  | write stage bit live port resources =>
    obtain ⟨origin,originEntry,replayEq,progress⟩ :=
      prefix_testing_origin input C hretained accounting budget positive small sample path active stage live.2
    have same : origin = history := Option.some.inj (originEntry.symm.trans entry)
    subst origin
    have currentTarget : entryTarget I budget stage state.history = some p :=
      (entryTarget_congr budget stage _ _ replayEq).symm.trans target
    obtain ⟨cache,_replay,_healthy,_valid,candidate,targetEq⟩ :=
      prefix_open_testing input C hretained.1 accounting budget positive small sample.1 (input.truthAt sample.2)
        (worldTapes input sample.2) path active stage live.2 port
    have raw := PRetCompletion.rule_raw_of_ne_abandon input budget none sample.1 state.history (.write stage bit)
      (by intro impossible; cases impossible) selected
    have alphabet : ∀ symbol ∈ historyObservations state.history stage, symbol < (input.experiment stage).alphabetSize :=
      fun symbol member => prefix_historyObservation_alphabet input C .uncapped accounting (retainedRule input budget none)
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) path stage symbol member
    obtain ⟨hit,map⟩ := testing_write_hit input state.history cache stage p bit (targetEq.symm.trans currentTarget)
      alphabet (candidate.symm.trans raw)
    have valid := entryTarget_valid budget stage history p target
    have boundary := (prefix_historyObservationWord_hits_iff input C .uncapped accounting
      (retainedRule input budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) path stage alphabet
      p valid.1 (lt_of_le_of_lt valid.2 (by norm_num))).mp hit
    have upper := ((input.experiment stage).posteriorThresholdStop_le_iff p (worldTapes input sample.2 stage)
      (state.ledger.reviews stage).toNat).mpr ⟨_,le_rfl,boundary⟩
    have finite := prefix_reviews_natCast_toNat input C .uncapped accounting (retainedRule input budget none)
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) path stage
    have lower : ((state.ledger.reviews stage).toNat : ℕ∞) ≤
        (input.experiment stage).posteriorThresholdStop p (worldTapes input sample.2 stage) := by
      rw [finite]
      exact progress port p currentTarget
    have stop := le_antisymm upper lower
    have mapAtStop := prefix_historyObservationWord_MAP_at_stop input C .uncapped accounting
      (retainedRule input budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) path stage alphabet p stop
    have worldTape : worldTapes input sample.2 stage = (sample.2 stage).2 := by funext k; rfl
    exact ⟨by simpa only [worldTape] using stop,by simpa only [worldTape] using map.trans mapAtStop⟩

end PRetRiskMassFlow
