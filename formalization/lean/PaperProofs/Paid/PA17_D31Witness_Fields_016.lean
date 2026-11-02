module

public import PaperProofs.Paid.PA17_D31Witness_Success_015

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Paid.PA17D31WitnessFields016

open Common Common.Native PA17D31WitnessPolicy008 PA17D31WitnessCompletion009
open PA17D31WitnessCount014 PA17D31WitnessSuccess015

/-- Exactly the eight original witness fields. The independent minimum-risk
statement and the final numerical inequalities remain with DLower. -/
def WitnessFields (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (allocation : Deadline)
    (policy : Policy (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) Unit) : Prop :=
  let C := P.retainedPaymentExampleContract allocation
  let accounting := blindCallAccounting P.sharedInstance
  (∀ (sample : Unit × (P.input fee hfee).World) (n : ℕ) (stage : P.sharedInstance.Stage),
    (run (P.input fee hfee) C .native accounting policy.rule sample n).ledger.reviews stage = 0) ∧
  (∀ sample : Unit × (P.input fee hfee).World, ∃ n : ℕ,
    allWritten (run (P.input fee hfee) C .native accounting policy.rule sample n).ledger) ∧
  (∀ (sample : Unit × (P.input fee hfee).World) (n : ℕ) (stage : P.sharedInstance.Stage) (bit : Bool),
    (run (P.input fee hfee) C .native accounting policy.rule sample n).ledger.written stage = some bit → bit = false) ∧
  (∀ sample : Unit × (P.input fee hfee).World,
    runRepairCount (P.input fee hfee) C .native accounting policy.rule sample =
      if P.blindErrorCount fee hfee sample = P.certificate.stages then 0
      else (P.blindErrorCount fee hfee sample : ℝ≥0∞)) ∧
  risk (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ()) = P.targetRisk ∧
  expectedObservationBill (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
  expectedRepairCount (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ()) =
    ENNReal.ofReal ((P.certificate.stages : ℝ) / 2 - P.certificate.stages * (P.certificate.risk : ℝ)) ∧
  expectedBill (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ()) =
    ENNReal.ofReal (fee : ℝ) *
      expectedRepairCount (P.input fee hfee) C .native accounting policy.rule (Measure.dirac ())

theorem nativePolicy_fields_of_assignmentMass (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (hK : P.tools = P.certificate.stages - 1)
    (hmass : (P.input fee hfee).seededWorldLaw (Measure.dirac ())
      {sample | P.blindErrorCount fee hfee sample = P.certificate.stages} = P.targetRisk) :
    WitnessFields P fee hfee allocation (nativePolicy P fee hfee allocation) := by
  have hd : 0 ≤ (P.certificate.risk : ℝ) := by exact_mod_cast P.certificate.risk_pos.le
  have hs : (P.certificate.risk : ℝ) ≤ 1 / 2 := by
    have hle : (P.certificate.risk : ℝ) ≤ ((1 / 64 : ℚ) : ℝ) := Rat.cast_le.mpr P.certificate.risk_le
    norm_num at hle
    linarith
  exact ⟨nativePolicy_reviews_zero P fee hfee allocation,
    nativePolicy_allWritten P fee hfee allocation,
    nativePolicy_written_false P fee hfee allocation,
    nativePolicy_runRepairCount P fee hfee allocation hK,
    nativePolicy_risk_of_assignment_mass P fee hfee allocation hK hmass,
    nativePolicy_expectedObservationBill P fee hfee allocation,
    PA17D31WitnessCost005.expectedRepairCount_of_pathCount P fee hfee
      (P.retainedPaymentExampleContract allocation) .native (blindCallAccounting P.sharedInstance)
      (nativePolicy P fee hfee allocation) (P.certificate.risk : ℝ) hd hs hmass
      (nativePolicy_runRepairCount P fee hfee allocation hK),
    nativePolicy_expectedBill P fee hfee allocation⟩

theorem exists_witness_of_assignmentMass (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (hK : P.tools = P.certificate.stages - 1)
    (hmass : (P.input fee hfee).seededWorldLaw (Measure.dirac ())
      {sample | P.blindErrorCount fee hfee sample = P.certificate.stages} = P.targetRisk) :
    ∃ policy : Policy (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
        (blindCallAccounting P.sharedInstance) Unit,
      WitnessFields P fee hfee allocation policy :=
  ⟨nativePolicy P fee hfee allocation, nativePolicy_fields_of_assignmentMass P fee hfee allocation hK hmass⟩

end PaperProofs.Paid.PA17D31WitnessFields016
