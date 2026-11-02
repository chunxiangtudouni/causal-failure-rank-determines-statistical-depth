module

public import PaperProofs.Common.NativePenalty

/-!
With caps removed, native normal-call bookkeeping cannot change visible
information, task success or variable charges. This statement is deliberately
restricted to the uncapped comparator; it does not change native quotas or H0.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PaperProofs.Common.Native

variable {I : Instance}

def State.withNormalCalls (s : State I) (calls : ℕ∞) : State I :=
  { s with ledger := {s.ledger with normalCalls := calls} }

@[simp] theorem State.withNormalCalls_twice (s : State I) (a b : ℕ∞) :
    (s.withNormalCalls a).withNormalCalls b = s.withNormalCalls b := rfl

@[simp] theorem State.withNormalCalls_self (s : State I) :
    s.withNormalCalls s.ledger.normalCalls = s := by cases s; rfl

@[simp] theorem State.withNormalCalls_history (s : State I) (calls : ℕ∞) :
    (s.withNormalCalls calls).history = s.history := rfl

@[simp] theorem State.withNormalCalls_halted (s : State I) (calls : ℕ∞) :
    (s.withNormalCalls calls).halted = s.halted := rfl

@[simp] theorem State.withNormalCalls_cursor (s : State I) (calls : ℕ∞) :
    (s.withNormalCalls calls).cursor = s.cursor := rfl

theorem record_withNormalCalls (accounting accounting' : NormalAccounting I) (s : State I)
    (action : Action I) (responses : List (VisibleEvent I)) (L : Ledger I)
    (cursor : ℕ) (halted : Bool) (calls : ℕ∞) :
    record accounting' (s.withNormalCalls calls) action responses
      {L with normalCalls := calls} cursor halted =
        (record accounting s action responses L cursor halted).withNormalCalls
          (calls + accounting' s.history action responses) := rfl

theorem reviewLedger_withNormalCalls (s : State I) (i : I.Stage) (calls : ℕ∞) :
    reviewLedger (s.withNormalCalls calls) i = {reviewLedger s i with normalCalls := calls} := rfl

theorem reportedWriteLedger_withNormalCalls (C : Contract I) (s : State I)
    (i : I.Stage) (bit : Bool) (calls : ℕ∞) :
    reportedWriteLedger C (s.withNormalCalls calls) i bit =
      {reportedWriteLedger C s i bit with normalCalls := calls} := by
  classical
  have hguard : allWritten (writeLedger (s.withNormalCalls calls) i bit) =
      allWritten (writeLedger s i bit) := rfl
  dsimp only [reportedWriteLedger]
  rw [hguard]
  by_cases hr : C.reporting = .early
  · simp only [hr, ↓reduceIte]; rfl
  · simp only [hr, ↓reduceIte]
    by_cases hw : allWritten (writeLedger s i bit)
    · simp only [hw, ↓reduceIte]; rfl
    · simp only [hw, ↓reduceIte]; rfl

theorem writeResponses_withNormalCalls (C : Contract I) (s : State I)
    (i : I.Stage) (bit : Bool) (calls : ℕ∞) :
    writeResponses C (s.withNormalCalls calls) i bit = writeResponses C s i bit := rfl

theorem allocateLedger_withNormalCalls (s : State I) (h : MismatchHandle I) (r : I.Tool)
    (calls : ℕ∞) :
    allocateLedger (s.withNormalCalls calls) h r =
      {allocateLedger s h r with normalCalls := calls} := rfl

theorem executeLedger_withNormalCalls (s : State I) (h : MismatchHandle I) (r : I.Tool)
    (calls : ℕ∞) :
    executeLedger (s.withNormalCalls calls) h r =
      {executeLedger s h r with normalCalls := calls} := rfl

theorem advanceLedger_withNormalCalls (s : State I) (i : I.Stage) (calls : ℕ∞) :
    advanceLedger (s.withNormalCalls calls) i = {advanceLedger s i with normalCalls := calls} := rfl

theorem stopState_withNormalCalls (s : State I) (abandon : Bool) (calls : ℕ∞) :
    stopState (s.withNormalCalls calls) abandon = (stopState s abandon).withNormalCalls calls := rfl

/-- Transport every actual action, including actions after permanent failure.
Only the unobserved normal-call counter is allowed to differ. -/
theorem step_reaccount (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (hstep : Step input C .uncapped accounting tapes s action s') (calls : ℕ∞) :
    ∃ calls', Step input C .uncapped accounting' tapes
      (s.withNormalCalls calls) action (s'.withNormalCalls calls') := by
  cases hstep with
  | review i live port _ =>
    let responses : List (VisibleEvent I) := [.observation i (tapes i (s.ledger.reviews i).toNat).val]
    refine ⟨calls + accounting' s.history (.review i) responses, ?_⟩
    have h : Step input C .uncapped accounting' tapes (s.withNormalCalls calls) (.review i)
        (record accounting' (s.withNormalCalls calls) (.review i) responses
          (reviewLedger (s.withNormalCalls calls) i) s.cursor false) :=
      .review _ i live port (Or.inl rfl)
    simpa only [reviewLedger_withNormalCalls, record_withNormalCalls accounting accounting'] using h
  | write i bit live port _ =>
    refine ⟨calls + accounting' s.history (.write i bit) (writeResponses C s i bit), ?_⟩
    have h := Step.write (input := input) (C := C) (mode := ResourceMode.uncapped)
      (accounting := accounting') (tapes := tapes) (s.withNormalCalls calls) i bit live port (Or.inl rfl)
    simpa only [reportedWriteLedger_withNormalCalls, writeResponses_withNormalCalls,
      record_withNormalCalls accounting accounting', State.withNormalCalls_cursor] using h
  | allocate h r active handle compatible unused unallocated window _ =>
    refine ⟨calls + accounting' s.history (.allocate h r) [.committed h r], ?_⟩
    have hs := Step.allocate (input := input) (C := C) (mode := ResourceMode.uncapped)
      (accounting := accounting') (tapes := tapes) (s.withNormalCalls calls) h r active handle
      compatible unused unallocated window (Or.inl rfl)
    simpa only [allocateLedger_withNormalCalls, record_withNormalCalls accounting accounting',
      State.withNormalCalls_cursor] using hs
  | execute h r active handle compatible committed unused uncorrected window _ =>
    refine ⟨calls + accounting' s.history (.execute h r) [.executed h r], ?_⟩
    have hs := Step.execute (input := input) (C := C) (mode := ResourceMode.uncapped)
      (accounting := accounting') (tapes := tapes) (s.withNormalCalls calls) h r active handle
      compatible committed unused uncorrected window (Or.inl rfl)
    simpa only [executeLedger_withNormalCalls, record_withNormalCalls accounting accounting',
      State.withNormalCalls_cursor] using hs
  | advance i live written _ =>
    refine ⟨calls + accounting' s.history (.advance i) [.advanced i], ?_⟩
    have hs := Step.advance (input := input) (C := C) (mode := ResourceMode.uncapped)
      (accounting := accounting') (tapes := tapes) (s.withNormalCalls calls) i live written (Or.inl rfl)
    simpa only [advanceLedger_withNormalCalls, record_withNormalCalls accounting accounting',
      State.withNormalCalls_cursor] using hs
  | stop active =>
    exact ⟨calls, by simpa only [stopState_withNormalCalls] using
      (Step.stop (input := input) (C := C) (mode := ResourceMode.uncapped)
        (accounting := accounting') (tapes := tapes) (s.withNormalCalls calls) active)⟩
  | abandon active =>
    exact ⟨calls, by simpa only [stopState_withNormalCalls] using
      (Step.abandon (input := input) (C := C) (mode := ResourceMode.uncapped)
        (accounting := accounting') (tapes := tapes) (s.withNormalCalls calls) active)⟩

variable {Seed : Type*}

theorem prefix_reaccount (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting policy seed truth tapes n s) :
    ∃ calls, Prefix input C .uncapped accounting' policy seed truth tapes n (s.withNormalCalls calls) := by
  induction hp with
  | initial => exact ⟨0, .initial⟩
  | next _ step ih =>
    obtain ⟨calls, hp'⟩ := ih
    obtain ⟨calls', step'⟩ := step_reaccount input C accounting accounting' tapes step calls
    exact ⟨calls', .next hp' step'⟩

theorem legalRule_reaccount (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting policy) :
    LegalRule input C .uncapped accounting' policy := by
  intro seed truth tapes n s hp hactive
  obtain ⟨calls, hp'⟩ := prefix_reaccount input C accounting' accounting policy seed truth tapes hp
  obtain ⟨s', hs'⟩ := hlegal seed truth tapes n _ hp' hactive
  obtain ⟨calls', hnext⟩ := step_reaccount input C accounting accounting' tapes hs' s.ledger.normalCalls
  exact ⟨s'.withNormalCalls calls', by simpa only [State.withNormalCalls_twice,
    State.withNormalCalls_self, State.withNormalCalls_history] using hnext⟩

/-- Actual interpreted paths agree in every component except normal calls. -/
theorem run_reaccount (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting policy) (sample : Seed × input.World) (n : ℕ) :
    ∃ calls, run input C .uncapped accounting' policy sample n =
      (run input C .uncapped accounting policy sample n).withNormalCalls calls := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨calls, heq⟩ := ih
    by_cases hh : (run input C .uncapped accounting policy sample n).halted = true
    · have hh' : (run input C .uncapped accounting' policy sample n).halted = true := by
        rw [heq, State.withNormalCalls_halted]
        exact hh
      rw [run_succ_of_halted input C .uncapped accounting' policy sample n hh',
        run_succ_of_halted input C .uncapped accounting policy sample n hh]
      exact ⟨calls, heq⟩
    · have ha := Bool.eq_false_iff.mpr hh
      have ha' : (run input C .uncapped accounting' policy sample n).halted = false := by
        rw [heq, State.withNormalCalls_halted]
        exact ha
      obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy hlegal sample n
      obtain ⟨next, hnext⟩ := hlegal sample.1 (input.truthAt sample.2)
        (worldTapes input sample.2) m _ hp ha
      obtain ⟨calls', hs'⟩ := step_reaccount input C accounting accounting'
        (worldTapes input sample.2) hnext calls
      have hnext' : Step input C .uncapped accounting' (worldTapes input sample.2)
          (run input C .uncapped accounting' policy sample n)
          (policy sample.1 (run input C .uncapped accounting' policy sample n).history)
          (next.withNormalCalls calls') := by
        rw [heq, State.withNormalCalls_history]
        exact hs'
      rw [run_succ_of_step input C .uncapped accounting' policy sample n _ ha' hnext',
        run_succ_of_step input C .uncapped accounting policy sample n _ ha hnext]
      exact ⟨calls', rfl⟩

theorem runSuccess_reaccount_iff (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting policy) (sample : Seed × input.World) :
    runSuccess input C .uncapped accounting' policy sample ↔
      runSuccess input C .uncapped accounting policy sample := by
  unfold runSuccess
  apply exists_congr
  intro n
  obtain ⟨calls, heq⟩ := run_reaccount input C accounting accounting' policy hlegal sample n
  rw [heq]
  rfl

theorem runObservationBill_reaccount_eq (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting policy) (sample : Seed × input.World) :
    runObservationBill input C .uncapped accounting' policy sample =
      runObservationBill input C .uncapped accounting policy sample := by
  unfold runObservationBill
  apply iSup_congr
  intro n
  obtain ⟨calls, heq⟩ := run_reaccount input C accounting accounting' policy hlegal sample n
  rw [heq]
  rfl

theorem runActualBill_reaccount_eq (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting policy) (sample : Seed × input.World) :
    runActualBill input C .uncapped accounting' policy sample =
      runActualBill input C .uncapped accounting policy sample := by
  unfold runActualBill
  apply iSup_congr
  intro n
  obtain ⟨calls, heq⟩ := run_reaccount input C accounting accounting' policy hlegal sample n
  rw [heq]
  rfl

section Measurable

variable [MeasurableSpace Seed]

def Policy.reaccount (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (policy : Policy input C .uncapped accounting Seed) :
    Policy input C .uncapped accounting' Seed where
  rule := policy.rule
  measurable_rule := policy.measurable_rule
  legal := legalRule_reaccount input C accounting accounting' policy.rule policy.legal

theorem risk_reaccount_eq (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting policy) (ν : Measure Seed) :
    risk input C .uncapped accounting' policy ν = risk input C .uncapped accounting policy ν := by
  apply congrArg (fun s : Set (Seed × input.World) => input.seededWorldLaw ν s)
  ext sample
  exact not_congr (runSuccess_reaccount_iff input C accounting accounting' policy hlegal sample)

theorem expectedObservationBill_reaccount_eq (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting policy) (ν : Measure Seed) :
    expectedObservationBill input C .uncapped accounting' policy ν =
      expectedObservationBill input C .uncapped accounting policy ν := by
  apply lintegral_congr
  exact runObservationBill_reaccount_eq input C accounting accounting' policy hlegal

theorem penaltyObjective_reaccount_eq (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting policy) (ν : Measure Seed) (penalty : ℝ≥0∞) :
    penaltyObjective input C .uncapped accounting' policy ν penalty =
      penaltyObjective input C .uncapped accounting policy ν penalty := by
  rw [penaltyObjective, expectedObservationBill_reaccount_eq input C accounting accounting' policy hlegal,
    risk_reaccount_eq input C accounting accounting' policy hlegal]
  rfl

end Measurable

theorem penaltyValue_reaccount_le (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (penalty : ℝ≥0∞) :
    penaltyValue input C accounting' penalty ≤ penaltyValue input C accounting penalty := by
  conv_rhs => unfold penaltyValue
  refine le_iInf fun SmallSeed => le_iInf fun m => ?_
  let : MeasurableSpace SmallSeed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun policy => ?_
  have h := penaltyValue_le_policy input C accounting' penalty ν
    (policy.reaccount input C accounting accounting')
  change penaltyValue input C accounting' penalty ≤
    penaltyObjective input C .uncapped accounting' policy.rule ν penalty at h
  rwa [penaltyObjective_reaccount_eq input C accounting accounting' policy.rule policy.legal] at h

theorem penaltyValue_reaccount_eq (input : StatisticalInput I) (C : Contract I)
    (accounting accounting' : NormalAccounting I) (penalty : ℝ≥0∞) :
    penaltyValue input C accounting' penalty = penaltyValue input C accounting penalty :=
  le_antisymm (penaltyValue_reaccount_le input C accounting accounting' penalty)
    (penaltyValue_reaccount_le input C accounting' accounting penalty)

end PaperProofs.Common.Native
