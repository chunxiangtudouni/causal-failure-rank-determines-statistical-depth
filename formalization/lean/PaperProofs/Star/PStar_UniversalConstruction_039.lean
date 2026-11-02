module

public import PaperProofs.Star.PStar_UniversalExpectedCost_038
public import PaperProofs.Star.PStar_UniversalIdealRisk_028
public import PaperProofs.Star.RootStarEnvelope_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarUniversalConstruction039

open Common Common.Native Parameters PStarLR PStarCurrentLegality006 PStarCurrentImmediate007
  PStarCurrentToolIdentity008 PStarUniversalIdealRisk028 PStarUniversalExpectedCost038

/-- Complete original C07 construction, using the SAME original real script,
contracts and actual all-path charges, with no added caller hypotheses. -/
theorem universalFirstCurrentConstruction (P : PaperProofs.Star.Parameters) : P.UniversalFirstCurrentConstruction := by
  intro C current accounting r positive quarter
  exact ⟨currentReferenceLegality P .universalFirst r none C accounting,
    universalFirstIdealRisk P C current accounting r positive quarter,
    universalExpectedObservationBound P C accounting r positive,
    immediateExecution P .universalFirst r none C current.1 accounting,
    currentToolIdentities P .universalFirst r none C accounting,
    referenceAllPathCharges_of_legal P .universalFirst .current r none C accounting
      (current_legal_uncapped P .universalFirst r none C accounting)⟩

theorem c07Claims (P : PaperProofs.Star.Parameters) : P.C07Claims :=
  ⟨universalFirstCurrentConstruction P, RootStarEnvelope.universalFirstEnvelopeAsymptotics P⟩

end PaperProofs.Star.PStarUniversalConstruction039
