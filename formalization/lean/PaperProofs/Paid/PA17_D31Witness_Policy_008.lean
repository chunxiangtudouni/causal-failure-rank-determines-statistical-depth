module

public import PaperProofs.Paid.PA17_D31Witness_001
public import PaperProofs.Paid.PA17_D31Witness_Guard_002
public import PaperProofs.Paid.PA17_D31Witness_Guard_003
public import PaperProofs.Paid.PA17_D31Witness_Cost_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid.PA17D31WitnessPolicy008

open Common Common.Native PA17D31Witness001 PA17D31WitnessGuard002 PA17D31WitnessGuard003

def blindRule (P : Parameters) : PolicyRule P.sharedInstance Unit :=
  mixedGuarded (blindCandidate P)

theorem blindRule_ne_review (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) :
    blindRule P seed history ≠ .review stage := by
  unfold blindRule mixedGuarded
  split
  · exact blindCandidate_ne_review P seed history stage
  · simp

theorem blindRule_write_false (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) (bit : Bool)
    (ha : blindRule P seed history = .write stage bit) : bit = false := by
  unfold blindRule mixedGuarded at ha
  split at ha
  · exact blindCandidate_write_false P seed history stage bit ha
  · cases ha

theorem blindRule_uncapped_legal (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) :
    LegalRule (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .uncapped
      (blindCallAccounting P.sharedInstance) (blindRule P) :=
  mixedGuarded_legal (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
    rfl rfl (blindCallAccounting P.sharedInstance) (blindCandidate P)

/-- A real native policy with the original H=4N+1 and H0=3N+1. -/
def nativePolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (allocation : Deadline) :
    Policy (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) Unit where
  rule := blindRule P
  measurable_rule := measurable_of_countable _
  legal := retainedExample_native_legal P fee hfee allocation (blindRule P)
    (blindRule_uncapped_legal P fee hfee allocation)
    (fun seed truth tapes _ _ hp => prefix_reviews_zero (P.input fee hfee)
      (P.retainedPaymentExampleContract allocation) .uncapped (blindCallAccounting P.sharedInstance)
      (blindRule P) (blindRule_ne_review P) seed truth tapes hp)

theorem nativePolicy_reviews_zero (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (sample : Unit × (P.input fee hfee).World) (n : ℕ)
    (stage : P.sharedInstance.Stage) :
    (run (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule sample n).ledger.reviews stage = 0 :=
  run_reviews_zero (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
    (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation)
    (blindRule_ne_review P) sample n stage

theorem nativePolicy_written_false (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (sample : Unit × (P.input fee hfee).World) (n : ℕ)
    (stage : P.sharedInstance.Stage) (bit : Bool)
    (hw : (run (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule sample n).ledger.written stage = some bit) :
    bit = false :=
  run_written_false (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
    (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation)
    (blindRule_write_false P) sample n stage bit hw

theorem nativePolicy_expectedObservationBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) :
    expectedObservationBill (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule (Measure.dirac ()) = 0 :=
  expectedObservationBill_zero (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
    (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation)
    (blindRule_ne_review P) (Measure.dirac ())

theorem nativePolicy_expectedBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) :
    expectedBill (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule (Measure.dirac ()) =
      ENNReal.ofReal (fee : ℝ) *
        expectedRepairCount (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
          (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule (Measure.dirac ()) :=
  PA17D31WitnessCost005.expectedBill_eq_fee_mul_expectedRepairs P fee hfee
    (P.retainedPaymentExampleContract allocation) .native (blindCallAccounting P.sharedInstance)
    (nativePolicy P fee hfee allocation) (blindRule_ne_review P) (Measure.dirac ())

end PaperProofs.Paid.PA17D31WitnessPolicy008
