module

public import PaperProofs.Paid.PDMenu_PaidBellmanLower_058
public import PaperProofs.Paid.PDMenu_PaidBellmanUpper_045
public import PaperProofs.Paid.PDMenu_EndpointMinimum_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Paid

theorem paidExactPenaltyBellman (P : Parameters) : P.ExactPaidPenaltyBellman := by
  intro fee hfee n k penalty hn hp
  exact le_antisymm (freshPaidPenalty_bellman_upper P fee hfee n k penalty hn hp)
    (freshPaidPenalty_bellman_lower P fee hfee n k penalty hn hp)

/-- The untouched original D16 conjunction; each of its four original
obligations is supplied as a conclusion, with no new proof premise. -/
theorem paidPenaltyProgramClaims (P : Parameters) : P.PaidPenaltyProgramClaims :=
  ⟨P.freshPaidPenaltyOriginalIdentification, paidSuccessorOrder P,
    paidExactPenaltyBellman P, paidEndpointMinimumExists P⟩

end PDMenu
