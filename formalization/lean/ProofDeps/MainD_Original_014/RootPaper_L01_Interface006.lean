module

import RootPaper_L01_Full003

/-! The complete proved L01 specification is exported as a nonexposed
header. The exact definition, its kernel equality and its implementation
proof stay in the registered dependency interface's private data. -/

public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Structure.LaminarTree.L01PaperClosure

def FullPaperClaims : Prop := RootPaper.L01.FullPaperClaims

end PaperProofs.Structure.LaminarTree.L01PaperClosure

namespace RootPaper.L01.Interface

theorem proved_full_paper :
    PaperProofs.Structure.LaminarTree.L01PaperClosure.FullPaperClaims :=
  RootPaper.L01.full_paper_claims

private theorem exact_specification :
    PaperProofs.Structure.LaminarTree.L01PaperClosure.FullPaperClaims =
      RootPaper.L01.FullPaperClaims := rfl

end RootPaper.L01.Interface

#print axioms RootPaper.L01.Interface.proved_full_paper
