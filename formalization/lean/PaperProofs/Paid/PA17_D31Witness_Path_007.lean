module

public import PaperProofs.Paid.PA17_D31Witness_001
public import PaperProofs.Common.NativeHorizon

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessPath007

open Common Common.Native MeasureTheory PA17D31Witness001

variable {I : Instance} {Seed : Type*}

theorem prefix_written_before_cursor (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s) :
    ∀ stage : I.Stage, stage.val < s.cursor → s.ledger.written stage ≠ none := by
  induction hp with
  | initial => intro stage h; exact (Nat.not_lt_zero _ h).elim
  | @next n s next hp hs ih =>
    generalize ha : rule seed s.history = action at hs
    cases hs with
    | write current bit live port resources =>
      classical
      intro stage hstage
      have hne : stage ≠ current := by
        intro heq
        subst stage
        have hc := live.2
        change current.val < s.cursor at hstage
        omega
      change (reportedWriteLedger C s current bit).written stage ≠ none
      simp only [reportedWriteLedger]
      split_ifs <;> simpa only [writeLedger, Function.update_of_ne hne] using ih stage hstage
    | advance current live written resources =>
      intro stage hstage
      change stage.val < s.cursor + 1 at hstage
      change s.ledger.written stage ≠ none
      by_cases hold : stage.val < s.cursor
      · exact ih stage hold
      · have heq : stage = current := by
          apply Fin.ext
          have hc := live.2
          omega
        simpa only [heq] using written
    | review | allocate | execute | stop | abandon => exact ih

theorem blindCandidate_ne_abandon (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance))
    (hbound : historyCursor history ≤ P.certificate.stages) :
    blindCandidate P seed history ≠ .abandon := by
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
    · rename_i hnotlt
      have heq : historyCursor history = P.certificate.stages := by omega
      rw [ite_eq_left heq]
      split
      · simp
      · split <;> simp

theorem blindCandidate_stop_cursor (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance)) (hactive : historyHalted history = false)
    (ha : blindCandidate P seed history = .stop) :
    historyCursor history = P.certificate.stages := by
  unfold blindCandidate at ha
  simp only [hactive, Bool.false_eq_true, ↓reduceIte] at ha
  split at ha
  · split at ha
    · cases ha
    · split at ha
      · split at ha <;> cases ha
      · cases ha
  · split at ha
    · assumption
    · cases ha

theorem prefix_halted_cursor (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (rule : PolicyRule P.sharedInstance Unit)
    (hmatch : ∀ seed truth tapes n s,
      Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
        (blindCallAccounting P.sharedInstance) rule seed truth tapes n s →
      s.halted = false → rule seed s.history = blindCandidate P seed s.history)
    (seed : Unit) (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) rule seed truth tapes n s)
    (hh : s.halted = true) : s.cursor = P.certificate.stages := by
  cases hp with
  | initial => cases hh
  | @next n s next hp hs =>
    have hactive := step_source_active (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) tapes hs
    have hm := hmatch seed truth tapes n s hp hactive
    have hc := prefix_historyCursor (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) rule seed truth tapes hp
    have hb := (prefix_cursorInvariant (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) rule seed truth tapes hp).bound
    rw [Parameters.stageCount_eq] at hb
    generalize ha : rule seed s.history = action at hs
    cases hs with
    | stop =>
      have hhist := prefix_historyHalted (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
        .native (blindCallAccounting P.sharedInstance) rule seed truth tapes hp
      have hstop := blindCandidate_stop_cursor P seed s.history (hhist.trans hactive) (hm.symm.trans ha)
      exact hc.symm.trans hstop
    | abandon =>
      exact (blindCandidate_ne_abandon P seed s.history (hc.symm ▸ hb) (hm.symm.trans ha)).elim
    | review | write | allocate | execute | advance => cases hh

/-- The original finite native horizon gives a completed writing phase once
the visible permission guard is proved nonbinding. No sample is omitted. -/
theorem run_allWritten_of_nonbinding (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (rule : PolicyRule P.sharedInstance Unit)
    (hlegal : LegalRule (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) rule)
    (hmatch : ∀ seed truth tapes n s,
      Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
        (blindCallAccounting P.sharedInstance) rule seed truth tapes n s →
      s.halted = false → rule seed s.history = blindCandidate P seed s.history)
    (sample : Unit × (P.input fee hfee).World) :
    ∃ n : ℕ, allWritten (run (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) rule sample n).ledger := by
  let stopIndex := nativeActionBound (P.retainedPaymentExampleContract allocation) + 1
  have hh := run_halted_nativeActionBound_succ (P.input fee hfee)
    (P.retainedPaymentExampleContract allocation) (blindCallAccounting P.sharedInstance) rule hlegal sample
  obtain ⟨m, _, hp⟩ := run_has_prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
    .native (blindCallAccounting P.sharedInstance) rule hlegal sample stopIndex
  have hc := prefix_halted_cursor P fee hfee allocation rule hmatch sample.1 _ _ hp hh
  refine ⟨stopIndex, ?_⟩
  intro stage
  apply prefix_written_before_cursor (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
    .native (blindCallAccounting P.sharedInstance) rule sample.1 _ _ hp stage
  rw [hc]
  exact stage_lt_stages P stage

end PaperProofs.Paid.PA17D31WitnessPath007
