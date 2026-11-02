module

public import PaperProofs.Common.HealthyPenaltyAsymptotics
public import PaperProofs.Common.FixedGraphPriceAssembly

/-!
The original fixed-input native price law. The independent penalty
asymptotics close the cap-independent lower half; the already proved
actual qualified reference controller supplies the upper and infinite-rank
parts. No pending asymptotic or controller-performance premise remains.
-/

@[expose] public section

namespace PaperProofs.Common

variable {I : Instance}

theorem StatisticalInput.nativeLowerPriceLaw (input : StatisticalInput I) :
    input.NativeLowerPriceLaw :=
  input.nativeLowerPriceLaw_of_penaltyAsymptotics input.penaltyAsymptotics

theorem StatisticalInput.fixedGraphPriceLaw (input : StatisticalInput I) :
    input.FixedGraphPriceLaw :=
  input.fixedGraphPriceLaw_of_nativeLower input.nativeLowerPriceLaw

end PaperProofs.Common
