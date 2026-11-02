module

import RootPaper_B23_Full004

/-! Public header for the complete proved B23 specification. Its exact
definition and implementation proof stay in this dependency module's
private data. A normal canonical theorem imports this header without
forcing the duplicate implementation modules into its public environment. -/

public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.B23PaperClosure

def FullPaperClaims : Prop := RootPaper.B23.FullPaperClaims

end PaperProofs.Common.Native.B23PaperClosure

namespace RootPaper.B23.Interface

theorem proved_full_paper :
    PaperProofs.Common.Native.B23PaperClosure.FullPaperClaims :=
  RootPaper.B23.full_paper_claims

private theorem exact_specification :
    PaperProofs.Common.Native.B23PaperClosure.FullPaperClaims =
      RootPaper.B23.FullPaperClaims := rfl

end RootPaper.B23.Interface

#print axioms RootPaper.B23.Interface.proved_full_paper
