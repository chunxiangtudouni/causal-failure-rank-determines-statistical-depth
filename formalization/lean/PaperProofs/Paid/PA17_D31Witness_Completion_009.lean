module

public import PaperProofs.Paid.PA17_D31Witness_Policy_008
public import PaperProofs.Paid.PA17_D31Witness_Path_007
public import PaperProofs.Paid.PA17_D31Witness_Nonbinding_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessCompletion009

open Common Common.Native MeasureTheory PA17D31Witness001 PA17D31WitnessGuard002
open PA17D31WitnessPolicy008 PA17D31WitnessPath007 PA17D31WitnessNonbinding006

theorem nativeRule_nonbinding (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (seed : Unit) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes n s) :
    blindRule P seed s.history = blindCandidate P seed s.history := by
  have hpu := prefix_native_to_uncapped (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
    (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp
  exact ite_eq_left (blindCandidate_allowed P fee hfee allocation (blindRule P) seed truth tapes hpu seed)

theorem nativePolicy_allWritten (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (sample : Unit × (P.input fee hfee).World) :
    ∃ n : ℕ, allWritten (run (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule sample n).ledger := by
  apply run_allWritten_of_nonbinding P fee hfee allocation (blindRule P)
    (nativePolicy P fee hfee allocation).legal
  intro seed truth tapes n s hp _
  exact nativeRule_nonbinding P fee hfee allocation seed truth tapes hp

end PaperProofs.Paid.PA17D31WitnessCompletion009
