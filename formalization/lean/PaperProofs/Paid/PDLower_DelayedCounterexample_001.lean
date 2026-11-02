module

/- Exact original D31 conjunction, combining the frozen actual native witness
with the all-Seed minimum and actual-mean numerical inequalities. -/

public import PaperProofs.Paid.PDLower_BlindMinimum_001
public import PaperProofs.Paid.PDLower_BlindNumeric_002
public import PaperProofs.Paid.PA17_D31Witness_Original_017

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

universe u

theorem retainedPaymentUsageCounterexample (P : Parameters) :
    P.RetainedPaymentUsageCounterexample.{u} := by
  intro hN hK hdelta fee hf allocation
  obtain ⟨policy, fields⟩ := PA17D31WitnessOriginal017.exists_original_witness P fee hf allocation hK hdelta
  obtain ⟨reviews, written, falseBits, pathCount, policyRisk, observations, repairs, bill⟩ := fields
  refine ⟨blindRiskMinimal P fee hf allocation, policy, reviews, written, falseBits,
    pathCount, policyRisk, observations, repairs, bill, ?_⟩
  exact delayedPayment_mean_numeric P hN fee hf (P.retainedPaymentExampleContract allocation)
    .native (blindCallAccounting P.sharedInstance) policy.rule (Measure.dirac ()) repairs

end PDLower
