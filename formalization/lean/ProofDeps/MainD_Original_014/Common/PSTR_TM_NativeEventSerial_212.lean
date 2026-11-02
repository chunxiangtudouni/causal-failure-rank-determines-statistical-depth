module
public import Common.PSTR_TM_NativeSerial_205

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeEventSerial212
open PaperProofs.Common.Native
variable {I : Instance}

/-- Proof-only projection of the ORIGINAL encoded event fields. No
timestamp, bound or certificate is added to a machine input. -/
def eventSerial : VisibleEvent I → Nat
  | .wrote _ _ serial => serial
  | .report _ _ serial => serial
  | .committed handle _ => handle.writeSerial
  | .executed handle _ => handle.writeSerial
  | _ => 0

private theorem writeLedger_serial_le (s : State I) (i : I.Stage) (bit : Bool)
    (hs : ∀ j, s.ledger.writeSerial j ≤ s.clock) (j : I.Stage) :
    (writeLedger s i bit).writeSerial j ≤ s.clock := by
  classical
  have hj := hs j
  simp only [writeLedger,Function.update_apply]
  split_ifs <;> omega

theorem writeResponses_serial_le (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool)
    (hs : ∀ j, s.ledger.writeSerial j ≤ s.clock) :
    ∀ event ∈ writeResponses C s i bit, eventSerial event ≤ s.clock := by
  classical
  intro event he
  simp only [writeResponses,List.mem_append] at he
  rcases he with hw | hr
  · have hh := List.mem_singleton.mp hw
    subst event
    exact Nat.le_refl _
  · split_ifs at hr
    · have hh := List.mem_singleton.mp hr
      subst event
      exact Nat.le_refl _
    · simp only [reportAll] at hr
      rcases List.mem_ofFn.mp hr with ⟨j,hj⟩
      subst event
      exact writeLedger_serial_le s i bit hs j
    · simp at hr

theorem record_serial_le (accounting : NormalAccounting I) (s : State I) (action : Action I)
    (responses : List (VisibleEvent I)) (L : Ledger I) (cursor : Nat) (halted : Bool)
    (old : ∀ event ∈ s.history, eventSerial event ≤ s.clock)
    (new : ∀ event ∈ responses, eventSerial event ≤ s.clock) :
    ∀ event ∈ (record accounting s action responses L cursor halted).history,
      eventSerial event ≤ (record accounting s action responses L cursor halted).clock := by
  intro event he
  simp only [record,List.mem_append] at he
  change eventSerial event ≤ s.clock + 1
  rcases he with he | he
  · exact Nat.le_succ_of_le (old event he)
  · exact Nat.le_succ_of_le (new event he)

theorem stop_serial_le (s : State I) (abandon : Bool)
    (old : ∀ event ∈ s.history, eventSerial event ≤ s.clock) :
    ∀ event ∈ (stopState s abandon).history, eventSerial event ≤ (stopState s abandon).clock := by
  classical
  intro event he
  simp only [stopState,List.mem_append,List.mem_singleton] at he
  change eventSerial event ≤ s.clock + 1
  rcases he with he | he
  · exact Nat.le_succ_of_le (old event he)
  · subst event
    cases abandon <;> exact Nat.zero_le _

/-- All historical serial fields, including old reports and committed /
executed handles, are bounded by the current actual clock. All reporting
modes and every legal failed path are included. -/
theorem prefix_eventSerial_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    ∀ event ∈ s.history, eventSerial event ≤ s.clock := by
  induction hp with
  | initial => intro event he; simp [initial] at he
  | @next n s next earlier step ih =>
    have hledger := PSTRTMNativeSerial205.prefix_ledger_serial_le input C mode accounting policy seed truth tapes earlier
    generalize haction : policy seed s.history = action at step
    cases step with
    | review =>
      apply record_serial_le _ _ _ _ _ _ _ ih
      intro event he
      have hh := List.mem_singleton.mp he
      subst event
      exact Nat.zero_le _
    | write =>
      apply record_serial_le _ _ _ _ _ _ _ ih
      exact writeResponses_serial_le _ _ _ _ hledger
    | allocate key _ _ hv _ _ _ _ _ =>
      apply record_serial_le _ _ _ _ _ _ _ ih
      intro event he
      have hh := List.mem_singleton.mp he
      subst event
      change key.writeSerial ≤ s.clock
      rw [hv.2.1]
      exact hledger _
    | execute key _ _ hv _ _ _ _ _ _ =>
      apply record_serial_le _ _ _ _ _ _ _ ih
      intro event he
      have hh := List.mem_singleton.mp he
      subst event
      change key.writeSerial ≤ s.clock
      rw [hv.2.1]
      exact hledger _
    | advance =>
      apply record_serial_le _ _ _ _ _ _ _ ih
      intro event he
      have hh := List.mem_singleton.mp he
      subst event
      exact Nat.zero_le _
    | stop => exact stop_serial_le _ _ ih
    | abandon => exact stop_serial_le _ _ ih

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeEventSerial212
