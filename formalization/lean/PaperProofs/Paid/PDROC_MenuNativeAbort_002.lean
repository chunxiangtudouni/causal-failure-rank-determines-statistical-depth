module

public import PaperProofs.Paid.PDROC_MenuNativeAbort_001
public import PaperProofs.Paid.PDMenu_MenuAbortAssembly_124
public import PaperProofs.Paid.PDROC_MenuMeans_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid

namespace PDROC

/-- The exact last Native branch obligation, discharged by the unchanged
original interpreter's finite wrong-write abort proof. -/
theorem menuNativeAbortClaims (P : Parameters) : PDMenu.MenuNativeAbortClaims P := by
  intro N K table fee hfee C hC accounting sample cursor n clock hfit stage hstage hentry level reviews bad ha
    hstop hwrong habort
  exact menuEntryRunRecords_test_abort P N K table fee hfee C hC accounting sample cursor n clock hfit
    stage hstage hentry level reviews bad ha hstop hwrong habort

/-- Exact actual run/summary refinement. The finite-stage induction and
probability-one endpoint-stop set discharge every continuation premise. -/
theorem menuNativeSummaryRefinement (P : Parameters) : PDMenu.MenuNativeSummaryRefinement P :=
  PDMenu.menuNativeSummaryRefinement_of_abort P (menuNativeAbortClaims P)

/-- Original computed menu compiler means, now without any Native,
continuation, finite-expectation or other performance premise. -/
theorem menuCompilerMeans (P : Parameters) : P.MenuCompilerMeans :=
  menuCompilerMeans_of_nativeSummaryRefinement P (menuNativeSummaryRefinement P)

end PDROC
