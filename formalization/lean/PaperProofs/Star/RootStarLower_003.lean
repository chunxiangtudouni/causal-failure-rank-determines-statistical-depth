module

public import PaperProofs.Star.RootStarLower_002
public import PaperProofs.Retained.PRet_FreshRecursion_115

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootStarLower

theorem threePricesLower (P : PaperProofs.Star.Parameters) : P.ThreePricesLower :=
  threePricesLower_of_retained_recursion P
    (fun order => PaperProofs.Retained.PRetFreshRecursion115.freshPenaltyRecursion (P.input order))

end RootStarLower
