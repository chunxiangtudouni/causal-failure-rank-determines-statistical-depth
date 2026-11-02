module

public import RootPaper_B23_Interface007

set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.B23PaperClosure

/-- The complete paper specification, defined and proved in the bound
dependency interface, is consumed here at its exact public type. -/
public theorem full_paper_claims : FullPaperClaims :=
  RootPaper.B23.Interface.proved_full_paper

end PaperProofs.Common.Native.B23PaperClosure

#print axioms PaperProofs.Common.Native.B23PaperClosure.full_paper_claims
