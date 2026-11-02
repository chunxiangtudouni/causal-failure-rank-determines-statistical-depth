module

public import PaperProofs.Paid.PDROC_CalibratedAssembly_003
public import PaperProofs.Paid.PDROC_CalibratedLaw_013

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid

namespace PDROC

/-- The complete original D25 claim for every actual generated search
state. Actual runtime comparison, whole outcome law, observation comparison,
actual correction bills and recorded cost are all independently discharged. -/
theorem calibratedImplementationClaims (P : Parameters) : P.CalibratedImplementationClaims := by
  apply CalibratedAssembly.implementation_of_state_laws P
  intro fee hfee C accounting steps
  exact ⟨CalibratedLaw.calibratedState_executionSignatureLaw P fee hfee C accounting steps,
    CalibratedLaw.calibratedState_expectedObservationBill_le_four P fee hfee C accounting steps⟩

/-- The complete original D26 claim, using exactly the original contract
qualification for THIS fixed calibrated algorithm and the original value. -/
theorem calibratedNativeEightClaims (P : Parameters) : P.CalibratedNativeEightClaims :=
  CalibratedAssembly.nativeEight_of_implementation P (calibratedImplementationClaims P)

/-- All five complete original calibrated backend claims, with no
performance, duration, risk, cost or continuation supplied by the caller. -/
theorem calibratedBackendClaims (P : Parameters) : P.CalibratedBackendClaims :=
  CalibratedAssembly.backend_of_implementation P (calibratedImplementationClaims P)

end PDROC
