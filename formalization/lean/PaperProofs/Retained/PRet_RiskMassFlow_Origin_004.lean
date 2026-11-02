module

public import PaperProofs.Retained.PRet_RiskMassFlow_ReviewStrict_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory

namespace PRetRiskMassFlow

variable {I : Instance}

/-- A proof-only fact about actual Prefixes. The original replay cache is
constant throughout a current stage; an open port stays before its genuine
first posterior exit. Written ports are retained without a stopping premise. -/
def TestingOrigin (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (sample : Unit × input.World) (state : State I) (stage : I.Stage) : Prop :=
  ∃ history, entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some history ∧
    replayBudget I budget history stage.val = replayBudget I budget state.history stage.val ∧
    (state.ledger.written stage = none → ∀ p,
      entryTarget I budget stage state.history = some p →
      state.ledger.reviews stage ≤ (input.experiment stage).posteriorThresholdStop p (worldTapes input sample.2 stage))

set_option backward.isDefEq.respectTransparency.types false in
theorem prefix_testing_origin (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2)
    (sample : Unit × input.World) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n state) :
    ∀ (_active : state.halted = false) (stage : I.Stage), state.cursor = stage.val →
      TestingOrigin input C accounting budget sample state stage := by
  induction path with
  | initial =>
    intro _active stage cursor
    refine ⟨[],entryHistory_stageZero input C .uncapped accounting (retainedRule input budget none)
      stage cursor.symm sample,rfl,?_⟩
    intro _open p _target
    exact zero_le
  | @next n state next earlier step ih =>
    intro active stage cursor
    have oldRun := prefix_eq_run_sample input C accounting budget sample earlier
    have nextRun := prefix_eq_run_sample input C accounting budget sample (.next earlier step)
    have frame := PRetAlignment.step_replayBudget_past input C hretained.1 .uncapped accounting
      (retainedRule input budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier step budget
    have original := step
    generalize action : retainedRule input budget none sample.1 state.history = selected at step
    cases step with
    | review current live port resources =>
      change state.cursor = stage.val at cursor
      have same : current = stage := Fin.ext (live.2.symm.trans cursor)
      subst current
      rw [cursor] at frame
      obtain ⟨history,entry,replayEq,progress⟩ := ih live.1 stage cursor
      refine ⟨history,entry,replayEq.trans frame.symm,?_⟩
      intro _open p target
      have oldTarget := (entryTarget_congr budget stage _ _ frame).symm.trans target
      have strict := review_stop_strict input C hretained.1 accounting budget positive small sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) earlier live.1 stage cursor port p oldTarget action
        (progress port p oldTarget)
      have finite := prefix_reviews_natCast_toNat input C .uncapped accounting (retainedRule input budget none)
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier stage
      have strictNat : ((state.ledger.reviews stage).toNat : ℕ∞) <
          (input.experiment stage).posteriorThresholdStop p (worldTapes input sample.2 stage) := by
        rw [finite]
        exact strict
      have successor := natCast_succ_le_of_lt (state.ledger.reviews stage).toNat _ strictNat
      simpa only [record,reviewLedger,Function.update_self,Nat.cast_add,Nat.cast_one,finite] using successor
    | write current bit live port resources =>
      change state.cursor = stage.val at cursor
      have same : current = stage := Fin.ext (live.2.symm.trans cursor)
      subst current
      rw [cursor] at frame
      obtain ⟨history,entry,replayEq,_progress⟩ := ih live.1 stage cursor
      refine ⟨history,entry,replayEq.trans frame.symm,?_⟩
      intro openPort
      change (reportedWriteLedger C state stage bit).written stage = none at openPort
      simp only [reportedWriteLedger,hretained.1,↓reduceIte,writeLedger,Function.update_self] at openPort
      cases openPort
    | advance current live written resources =>
      change state.cursor+1 = stage.val at cursor
      have before : state.cursor < stage.val := by omega
      have entry := entryHistory_at_increment input C hretained accounting budget sample n state _ stage
        oldRun nextRun before cursor
      refine ⟨_,entry,rfl,?_⟩
      intro _open p _target
      have zero := (prefix_cursorInvariant input C .uncapped accounting (retainedRule input budget none)
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier).future_reviews stage before
      change state.ledger.reviews stage ≤ _
      rw [zero]
      exact zero_le
    | allocate handle tool oldActive valid compatible unused unallocated window resources =>
      change state.cursor = stage.val at cursor
      rw [cursor] at frame
      obtain ⟨history,entry,replayEq,progress⟩ := ih oldActive stage cursor
      refine ⟨history,entry,replayEq.trans frame.symm,?_⟩
      intro openPort p target
      have oldTarget := (entryTarget_congr budget stage _ _ frame).symm.trans target
      exact progress openPort p oldTarget
    | execute handle tool oldActive valid compatible committed unused uncorrected window resources =>
      change state.cursor = stage.val at cursor
      rw [cursor] at frame
      obtain ⟨history,entry,replayEq,progress⟩ := ih oldActive stage cursor
      refine ⟨history,entry,replayEq.trans frame.symm,?_⟩
      intro openPort p target
      have oldTarget := (entryTarget_congr budget stage _ _ frame).symm.trans target
      exact progress openPort p oldTarget
    | stop | abandon => cases active

end PRetRiskMassFlow
