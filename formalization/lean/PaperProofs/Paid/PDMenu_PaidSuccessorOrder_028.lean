module

public import PaperProofs.Paid.RootPaidToolTransport005
public import PaperProofs.Paid.PDMenu_SuccessorAssembly_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

/-- Original D16 successor-order target, now supplied by a genuine all-policy
actual-cost tool-injection proof. All n/k, fee=0 and original finite lambda
remain quantified by the unmodified target. -/
theorem paidSuccessorOrder (P : PaperProofs.Paid.Parameters) : P.PaidSuccessorOrder :=
  paidSuccessorOrder_of_tools_antitone P (RootPaidToolTransport.freshPaidPenalty_tools_antitone P)

end PDMenu
