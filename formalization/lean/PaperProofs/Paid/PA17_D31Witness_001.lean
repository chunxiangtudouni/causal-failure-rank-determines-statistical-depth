module

public import PaperProofs.Paid.BridgeClaims
public import PaperProofs.Paid.MenuCompiler

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid.PA17D31Witness001

open Common Common.Native

theorem stage_lt_stages (P : Parameters) (stage : P.sharedInstance.Stage) :
    stage.val < P.certificate.stages := by
  have h : stage.val < P.sharedInstance.stageCount := stage.isLt
  simpa only [P.stageCount_eq] using h

/-- Keep the policy's original instance explicit at history-rewrite boundaries. -/
def blindUnusedTool (P : Parameters) (history : List (VisibleEvent P.sharedInstance)) :
    Option P.sharedInstance.Tool :=
  P.menuUnusedTool P.certificate.stages P.tools history

/-- This predicate reads only already returned reports, with no hidden-world input. -/
def allReportsWrong (P : Parameters) (history : List (VisibleEvent P.sharedInstance)) : Prop :=
  ∀ stage : P.sharedInstance.Stage, (historyReport history stage).map Prod.fst = some true

instance (P : Parameters) (history : List (VisibleEvent P.sharedInstance)) :
    Decidable (allReportsWrong P history) := by
  unfold allReportsWrong
  infer_instance

/-- Writes every stage before making any physical execution. The current stage
gets a real commitment when its report is wrong and a real unused tool exists.
At the barrier the all-wrong path pays nothing; every other path executes each
pending real commitment. The separate guard handles malformed histories. -/
def blindCandidate (P : Parameters) : PolicyRule P.sharedInstance Unit := fun _ history =>
  if historyHalted history then .stop else
  if hstage : historyCursor history < P.certificate.stages then
    let stage : P.sharedInstance.Stage := ⟨historyCursor history,
      by simpa [Parameters.sharedInstance, Instance.stageCount] using hstage⟩
    match historyWrite history stage with
    | none => .write stage false
    | some _ =>
        if historyValidHandle history ⟨stage, historyWriteSerial history stage⟩ ∧
            ¬ (historyCommitments history).any (fun pair => pair.1.stage == stage) then
          match blindUnusedTool P history with
          | some tool => .allocate ⟨stage, historyWriteSerial history stage⟩ tool
          | none => .advance stage
        else .advance stage
  else if historyCursor history = P.certificate.stages then
    if allReportsWrong P history then .stop else
    match (historyCommitments history).find? (fun pair =>
        !(historyExecutions history).any (fun e => e.1.stage == pair.1.stage)) with
    | some pair => .execute pair.1 pair.2
    | none => .stop
  else .abandon

theorem blindCandidate_ne_review (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) :
    blindCandidate P seed history ≠ .review stage := by
  unfold blindCandidate
  split
  · simp
  · split
    · dsimp only
      split
      · simp
      · split
        · split <;> simp
        · simp
    · split
      · split
        · simp
        · split <;> simp
      · simp

theorem blindCandidate_write_false (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) (bit : Bool)
    (ha : blindCandidate P seed history = .write stage bit) : bit = false := by
  unfold blindCandidate at ha
  split at ha
  · cases ha
  · split at ha
    · dsimp only at ha
      split at ha
      · exact (Action.write.inj ha).2.symm
      · split at ha
        · split at ha <;> cases ha
        · cases ha
    · split at ha
      · split at ha
        · cases ha
        · split at ha <;> cases ha
      · cases ha

section GenericPathFacts

variable {I : Instance} {Seed : Type*}

/-- No-review is proved on every genuine prefix, including failing ones. -/
theorem prefix_reviews_zero (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hnoreview : ∀ seed history stage, rule seed history ≠ .review stage)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    ∀ stage, s.ledger.reviews stage = 0 := by
  induction hp with
  | initial => intro stage; rfl
  | @next n s next hp hs ih =>
    generalize ha : rule seed s.history = action at hs
    cases hs with
    | review stage => exact (hnoreview seed s.history stage ha).elim
    | write =>
      classical
      simp only [record, reportedWriteLedger]
      split_ifs <;> exact ih
    | allocate | execute | advance | stop | abandon => exact ih

/-- The false-written invariant does not assume eventual success. -/
theorem prefix_written_false (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hfalse : ∀ seed history stage bit, rule seed history = .write stage bit → bit = false)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    ∀ stage bit, s.ledger.written stage = some bit → bit = false := by
  induction hp with
  | initial => intro stage bit hb; cases hb
  | @next n s next hp hs ih =>
    generalize ha : rule seed s.history = action at hs
    cases hs with
    | write stage bit =>
      classical
      have hb := hfalse seed s.history stage bit ha
      intro other value hv
      have hw : (reportedWriteLedger C s stage bit).written =
          Function.update s.ledger.written stage (some bit) := by
        simp only [reportedWriteLedger]
        split_ifs <;> rfl
      change (reportedWriteLedger C s stage bit).written other = some value at hv
      rw [hw] at hv
      by_cases heq : other = stage
      · subst other
        simpa only [Function.update_self, Option.some.injEq, hb] using hv.symm
      · exact ih other value (by simpa only [Function.update_of_ne heq] using hv)
    | review | allocate | execute | advance | stop | abandon => exact ih

variable [MeasurableSpace Seed]

theorem run_reviews_zero (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (hnoreview : ∀ seed history stage, policy.rule seed history ≠ .review stage)
    (sample : Seed × input.World) (n : ℕ) (stage : I.Stage) :
    (run input C mode accounting policy.rule sample n).ledger.reviews stage = 0 := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C mode accounting policy.rule policy.legal sample n
  exact prefix_reviews_zero input C mode accounting policy.rule hnoreview sample.1 _ _ hp stage

theorem run_written_false (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (hfalse : ∀ seed history stage bit, policy.rule seed history = .write stage bit → bit = false)
    (sample : Seed × input.World) (n : ℕ) (stage : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting policy.rule sample n).ledger.written stage = some bit) :
    bit = false := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C mode accounting policy.rule policy.legal sample n
  exact prefix_written_false input C mode accounting policy.rule hfalse sample.1 _ _ hp stage bit hw

theorem expectedObservationBill_zero (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : Policy input C mode accounting Seed)
    (hnoreview : ∀ seed history stage, policy.rule seed history ≠ .review stage) (ν : Measure Seed) :
    expectedObservationBill input C mode accounting policy.rule ν = 0 := by
  have hobs (sample : Seed × input.World) :
      runObservationBill input C mode accounting policy.rule sample = 0 := by
    simp [runObservationBill, Ledger.observationBill,
      run_reviews_zero input C mode accounting policy hnoreview]
  simp [expectedObservationBill, hobs]

end GenericPathFacts

end PaperProofs.Paid.PA17D31Witness001
