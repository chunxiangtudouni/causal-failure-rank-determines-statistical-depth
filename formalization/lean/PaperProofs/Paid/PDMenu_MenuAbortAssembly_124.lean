module

public import PaperProofs.Paid.PDMenu_MenuFiniteEntryInduction_123

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Exact independent no-continuation branch goal. Its proof is still
required; this Prop definition is not an original Native/Means theorem. -/
def MenuNativeAbortClaims (P : Parameters) : Prop :=
  ∀ (N K : ℕ) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract (freshInstance N K)), C.IsCurrentPayment →
      ∀ (accounting : NormalAccounting (freshInstance N K))
        (sample : MenuSeed N K × (P.freshInput N K fee hfee).World),
        MenuAbortEntryRecords P N K table fee hfee C accounting sample

theorem menuNativePathAgreement_of_abort_records (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (hfinite : MenuEndpointFiniteSample P N K fee hfee sample)
    (habort : MenuAbortEntryRecords P N K table fee hfee C accounting sample) :
    MenuNativePathAgreement P N K table fee hfee C accounting sample := by
  have hentry : FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) 0 0 sample := by
    refine ⟨rfl, ?_⟩
    intro j hj
    exact ((Nat.not_lt_zero j) hj).elim
  have hrecords := menuEntryRunRecords_induction P N K table fee hfee C hC accounting sample hfinite habort
    N 0 0 (Nat.zero_add N) hentry
  exact menuNativePathAgreement_of_root_records P N K table fee hfee C hC.1.1 accounting sample hrecords

/-- After the independent actual abort branch is proved, all Native
continuation premises are eliminated and the original record refinement
follows on the proved original probability-one finite-stop set. -/
theorem menuNativeSummaryRefinement_of_abort (P : Parameters) (habort : MenuNativeAbortClaims P) :
    MenuNativeSummaryRefinement P := by
  intro N K table fee hfee C hC accounting
  apply menuNativePathRecords_of_finite_agreement P N K table fee hfee C accounting
  intro sample hfinite
  exact menuNativePathAgreement_of_abort_records P N K table fee hfee C hC accounting sample hfinite
    (habort N K table fee hfee C hC accounting sample)

end PDMenu
