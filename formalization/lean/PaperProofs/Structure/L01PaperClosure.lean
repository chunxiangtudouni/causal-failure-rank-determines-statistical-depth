module

public import RootPaper_L01_Interface006

set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Structure.LaminarTree.L01PaperClosure

/-- Exact ordinary consumption of the complete bound paper specification. -/
public theorem full_paper_claims : FullPaperClaims :=
  RootPaper.L01.Interface.proved_full_paper

end PaperProofs.Structure.LaminarTree.L01PaperClosure

#print axioms PaperProofs.Structure.LaminarTree.L01PaperClosure.full_paper_claims
