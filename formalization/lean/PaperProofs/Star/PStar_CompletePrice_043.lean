module

public import PaperProofs.Star.PStar_NativePrice_042
public import PaperProofs.Star.PStar_UniversalConstruction_039
public import PaperProofs.Star.PStar_CountConstruction_040
public import PaperProofs.Star.RootStarOverflow_014
public import PaperProofs.Star.RootStarLower_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCompletePrice043

open Parameters PStarNativePrice042

/-- Complete original C12, with every construction, actual risk and fee,
cap qualification and lower comparison discharged by actual proofs. -/
theorem c12Claims (P : PaperProofs.Star.Parameters) : P.C12Claims :=
  c12Claims_of_interfaces P (PStarUniversalConstruction039.c07Claims P).1
    (PStarCountConstruction040.c08Claims P).1 (PStarLR.lateRetainedConstruction P)
    (RootStarOverflow.c11Claims.{0} P).2.2.2.2 (RootStarLower.threePricesLower P)

theorem threePrices (P : PaperProofs.Star.Parameters) : P.ThreePrices := (c12Claims P).1

end PaperProofs.Star.PStarCompletePrice043
