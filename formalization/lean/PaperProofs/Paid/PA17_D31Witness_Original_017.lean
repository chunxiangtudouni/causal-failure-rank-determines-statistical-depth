module

public import PaperProofs.Paid.PA17_D31Witness_Fields_016

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessOriginal017

open Common Common.Native PA17D31WitnessPolicy008 PA17D31WitnessFields016

/-- The actual original witness; the only numerical hypotheses are the
original K=N-1 and delta=2^-N. The DLower truth law is already proved. -/
theorem exists_original_witness (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (hK : P.tools = P.certificate.stages - 1)
    (hdelta : P.certificate.risk = (1 / 2 : ℚ) ^ P.certificate.stages) :
    ∃ policy : Policy (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
        (blindCallAccounting P.sharedInstance) Unit,
      WitnessFields P fee hfee allocation policy :=
  exists_witness_of_assignmentMass P fee hfee allocation hK
    (PA17D31WitnessLaw004.original_full_error_mass P fee hfee hdelta)

end PaperProofs.Paid.PA17D31WitnessOriginal017
