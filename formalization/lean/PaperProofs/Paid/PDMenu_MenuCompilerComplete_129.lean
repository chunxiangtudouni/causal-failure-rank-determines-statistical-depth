module

public import PaperProofs.Paid.PDMenu_MenuNativeValue_128
public import PaperProofs.Paid.PDROC_MenuNativeAbort_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Paid

/-- The full original D18 conjunction. All real Native branch obligations,
expected records and independent full-policy value identifications are
proved internally; no pending performance or continuation premise remains. -/
theorem menuCompilerClaims (P : Parameters) : P.MenuCompilerClaims :=
  ⟨P.menuTableDataCorrect, menuTableStatsBounds P, PDMenuNativeValue.menuTableValueCorrect P,
    PDROC.menuCompilerMeans P, menuCompilerGuardNonbinding P⟩

end PDMenu
