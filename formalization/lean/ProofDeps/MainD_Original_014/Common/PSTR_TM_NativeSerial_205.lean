module
public import Common.PSTR_TM_NativeHistory_204

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeSerial205
open PaperProofs.Common.Native
variable {I : Instance}

theorem reportedWrite_serial (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).writeSerial = Function.update s.ledger.writeSerial i s.clock := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

/-- Original ledger serials are actual old clocks, even on failed paths.
The invariant is proved from Step; it is not an extra input certificate. -/
theorem step_ledger_serial_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I}
    (h : Step input C mode accounting tapes s action next)
    (hs : ∀ i, s.ledger.writeSerial i ≤ s.clock) :
    ∀ i, next.ledger.writeSerial i ≤ next.clock := by
  classical
  intro j
  have hj := hs j
  cases h <;> simp only [record,reviewLedger,allocateLedger,executeLedger,advanceLedger,
    stopState,reportedWrite_serial]
  all_goals first
    | omega
    | (simp only [Function.update_apply]; split_ifs <;> omega)

theorem prefix_ledger_serial_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    ∀ i, s.ledger.writeSerial i ≤ s.clock := by
  induction hp with
  | initial => intro i; exact Nat.zero_le _
  | next _ step ih => exact step_ledger_serial_le input C mode accounting tapes step ih

theorem prefix_validHandle_serial_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (handle : MismatchHandle I) (hv : validHandle s handle) : handle.writeSerial ≤ s.clock := by
  rw [hv.2.1]
  exact prefix_ledger_serial_le input C mode accounting policy seed truth tapes hp _

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeSerial205
