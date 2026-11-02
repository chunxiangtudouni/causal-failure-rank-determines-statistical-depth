module

public import PaperProofs.Paid.PDMenu_MajorityOutputs_035

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

theorem measurable_majorityTapeDecision (P : Parameters) : Measurable (majorityTapeDecision P) := by
  have hword : Measurable (fun tape : P.experiment.Tape => (fun i : Fin P.certificate.t0 => tape i.val)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)
  exact (measurable_of_countable (fun word : Fin P.certificate.t0 → Fin 2 =>
    decide (0 ≤ menuWordScore (List.ofFn (fun i => (word i).val))))).comp hword

theorem majority_stage_error_eq (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) :
    (P.input fee hfee).seededWorldLaw (Measure.dirac ())
      {sample : Unit × (P.input fee hfee).World |
        majorityTapeDecision P (worldTapes (P.input fee hfee) sample.2 stage) ≠ (P.input fee hfee).truthAt sample.2 stage} =
      P.experiment.priorMass true * P.experiment.tapeLaw true {tape | majorityTapeDecision P tape ≠ true} +
      P.experiment.priorMass false * P.experiment.tapeLaw false {tape | majorityTapeDecision P tape ≠ false} := by
  let E : Set (Bool × P.experiment.Tape) := {pair | majorityTapeDecision P pair.2 ≠ pair.1}
  have hmE : MeasurableSet E := (measurableSet_eq_fun ((measurable_majorityTapeDecision P).comp measurable_snd) measurable_fst).compl
  have hmap := congrArg (fun law : Measure (Bool × P.experiment.Tape) => law E)
    ((P.input fee hfee).seededWorldLaw_coordinate (Measure.dirac ()) stage)
  have hmCoordinate : Measurable (fun sample : Unit × (P.input fee hfee).World => sample.2 stage) :=
    (measurable_pi_apply stage).comp measurable_snd
  have hcoordinate :=
    (Measure.map_apply (μ := (P.input fee hfee).seededWorldLaw (Measure.dirac ())) hmCoordinate hmE).symm.trans hmap
  calc
    _ = (P.input fee hfee).stageLaw stage E := hcoordinate
    _ = _ := by
      change ((P.experiment.priorMass true • (Measure.dirac true).prod (P.experiment.tapeLaw true) +
        P.experiment.priorMass false • (Measure.dirac false).prod (P.experiment.tapeLaw false)) E) = _
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hmE]
      rfl

/-- Actual native failure is bounded by the error events of the very same
original fixed words. This is an unconditional finite union bound, not an
assumed risk guarantee of the policy. -/
theorem majority_risk_le_sum_stage_errors (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    risk (P.input fee hfee) C.val .uncapped accounting P.majorityRule (Measure.dirac ()) ≤
      ∑ stage : P.sharedInstance.Stage, (P.input fee hfee).seededWorldLaw (Measure.dirac ())
        {sample : Unit × (P.input fee hfee).World |
          majorityTapeDecision P (worldTapes (P.input fee hfee) sample.2 stage) ≠
            (P.input fee hfee).truthAt sample.2 stage} := by
  unfold risk
  apply (measure_mono (majority_failure_subset P fee hfee C accounting)).trans
  simpa only [tsum_fintype] using measure_iUnion_le (fun stage : P.sharedInstance.Stage =>
    {sample : Unit × (P.input fee hfee).World |
      majorityTapeDecision P (worldTapes (P.input fee hfee) sample.2 stage) ≠
        (P.input fee hfee).truthAt sample.2 stage})

end PDMenu
