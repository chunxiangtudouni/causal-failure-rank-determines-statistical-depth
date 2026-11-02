module

public import PaperProofs.Paid.PDROC_MenuExpected_005
public import PaperProofs.Paid.PDMenu_MenuNativeRecordABI_114
public import PaperProofs.Paid.PDMenu_MenuBillCount_072

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.MenuMeans

/-- Transport the original three summary means along the complete original
seed/world reindexing and the actual Native record agreement. -/
theorem actual_records_of_pathRecords (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K))
    (accounting : NormalAccounting (freshInstance N K))
    (hrecords : PDMenu.MenuNativePathRecords P N K table fee hfee C accounting)
    (hmeans : PDMenu.MenuPathMeans P table N K) :
    expectedObservationBill (P.freshInput N K fee hfee) C .uncapped accounting
        (P.compiledMenuRule N K table) (menuSeedLaw N K) =
      ENNReal.ofReal ((menuEntryAt table N K).observation : ℝ) ∧
    expectedRepairCount (P.freshInput N K fee hfee) C .uncapped accounting
        (P.compiledMenuRule N K table) (menuSeedLaw N K) =
      ENNReal.ofReal ((menuEntryAt table N K).repairs : ℝ) ∧
    risk (P.freshInput N K fee hfee) C .uncapped accounting
        (P.compiledMenuRule N K table) (menuSeedLaw N K) =
      ENNReal.ofReal ((menuEntryAt table N K).failure : ℝ) := by
  let view := PDMenu.menuSampleFinView P N K fee hfee
  have hview := PDMenu.menuSampleFinView_measurePreserving P N K fee hfee
  have hobservation := PDMenu.measurable_menuPathObservation P table N K
  have hrepairs : Measurable (fun sample : PDMenu.MenuAnalysisSeed N × PDMenu.MenuAnalysisWorld P N =>
      ((PDMenu.menuPathSummary P table N K sample.1 sample.2).physicalRepairs : ℝ≥0∞)) :=
    (measurable_of_countable (fun count : ℕ => (count : ℝ≥0∞))).comp
      (PDMenu.measurable_menuPathRepairs P table N K)
  refine ⟨?_, ?_, ?_⟩
  · unfold expectedObservationBill
    calc
      _ = ∫⁻ sample, (PDMenu.menuPathSummary P table N K
            (view sample).1 (view sample).2).observation
            ∂(P.freshInput N K fee hfee).seededWorldLaw (menuSeedLaw N K) := by
        apply lintegral_congr_ae
        filter_upwards [hrecords] with sample hs
        exact hs.1
      _ = _ := (hview.lintegral_comp hobservation).trans hmeans.1
  · unfold expectedRepairCount
    calc
      _ = ∫⁻ sample, ((PDMenu.menuPathSummary P table N K
            (view sample).1 (view sample).2).physicalRepairs : ℝ≥0∞)
            ∂(P.freshInput N K fee hfee).seededWorldLaw (menuSeedLaw N K) := by
        apply lintegral_congr_ae
        filter_upwards [hrecords] with sample hs
        exact hs.2.1
      _ = _ := (hview.lintegral_comp hrepairs).trans hmeans.2.1
  · let failure : Set (PDMenu.MenuAnalysisSeed N × PDMenu.MenuAnalysisWorld P N) :=
      {sample | (PDMenu.menuPathSummary P table N K sample.1 sample.2).failure = true}
    have hfailure : MeasurableSet failure :=
      (PDMenu.measurable_menuPathFailure P table N K) (measurableSet_singleton true)
    unfold risk
    calc
      _ = ((P.freshInput N K fee hfee).seededWorldLaw (menuSeedLaw N K))
          (view ⁻¹' failure) := by
        apply measure_congr
        filter_upwards [hrecords] with sample hs
        apply propext
        change (¬ runSuccess _ _ _ _ _ sample) ↔
          (PDMenu.menuPathSummary P table N K (view sample).1 (view sample).2).failure = true
        rw [hs.2.2]
        cases (PDMenu.menuPathSummary P table N K (view sample).1 (view sample).2).failure <;> decide
      _ = _ := (hview.measure_preimage hfailure.nullMeasurableSet).trans hmeans.2.2

end PDROC.MenuMeans

namespace PDROC

/-- Exact original compiler means, conditional only on the original unproved
Native-to-summary refinement. This theorem alone does not close D18. -/
theorem menuCompilerMeans_of_nativeSummaryRefinement (P : Parameters)
    (hrefinement : PDMenu.MenuNativeSummaryRefinement P) : P.MenuCompilerMeans := by
  intro fee penalty hfee _hpenalty _hpenaltyUpper N K C hC accounting
  let table := P.solveMenuTable fee penalty K N
  have hrecords := hrefinement N K table fee hfee C hC accounting
  have hmeans := expectedMenuPathRecords P fee penalty N K N K le_rfl le_rfl
  have hactual := MenuMeans.actual_records_of_pathRecords P N K table fee hfee C accounting hrecords hmeans
  refine ⟨hactual.1, hactual.2.1, ?_, hactual.2.2⟩
  have hearly : C.reporting = .early := hC.1.1
  have hbill : expectedBill (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) (menuSeedLaw N K) =
      expectedObservationBill (P.freshInput N K fee hfee) C .uncapped accounting
        (P.compiledMenuRule N K table) (menuSeedLaw N K) +
      ENNReal.ofReal (fee : ℝ) * expectedRepairCount (P.freshInput N K fee hfee) C .uncapped accounting
        (P.compiledMenuRule N K table) (menuSeedLaw N K) :=
    PDMenu.constantFee_expectedBill_eq (P.freshInput N K fee hfee) fee
      (fun _ _ => rfl) C .uncapped accounting
      (P.compiledMenuPolicy N K table fee hfee C hearly accounting) (menuSeedLaw N K)
  change expectedBill (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) (menuSeedLaw N K) = _ at hbill ⊢
  rw [hbill, hactual.1, hactual.2.1]
  have hstats := PDMenu.solveMenuTable_stats P fee penalty N K N le_rfl K
  have ho : (0 : ℝ) ≤ (menuEntryAt table N K).observation := by exact_mod_cast hstats.1
  have hr : (0 : ℝ) ≤ (menuEntryAt table N K).repairs := by exact_mod_cast hstats.2.1
  have hf : (0 : ℝ) ≤ (fee : ℝ) := by exact_mod_cast hfee
  rw [Rat.cast_add, Rat.cast_mul, ENNReal.ofReal_add ho (mul_nonneg hf hr),
    ENNReal.ofReal_mul hf]

end PDROC
