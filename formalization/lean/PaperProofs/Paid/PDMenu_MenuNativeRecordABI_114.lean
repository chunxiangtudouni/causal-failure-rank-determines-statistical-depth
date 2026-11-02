module

public import PaperProofs.Paid.PDMenu_MenuSuffixSample_110
public import PaperProofs.Paid.PDMenu_MenuHaltedRecords_108
public import PaperProofs.Paid.PDMenu_MenuFiniteWorld_099

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Exact records of the unchanged original interpreter versus the frozen
analysis summary. This definition supplies no performance theorem. -/
def MenuNativePathAgreement (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K))
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World) : Prop :=
  let view := menuSampleFinView P N K fee hfee sample
  let record := menuPathSummary P table N K view.1 view.2
  runObservationBill (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample = record.observation ∧
    runRepairCount (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample = (record.physicalRepairs : ℝ≥0∞) ∧
    (runSuccess (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample ↔ record.failure = false)

def MenuNativePathRecords (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K))
    (accounting : NormalAccounting (freshInstance N K)) : Prop :=
  ∀ᵐ sample ∂(P.freshInput N K fee hfee).seededWorldLaw (menuSeedLaw N K),
    MenuNativePathAgreement P N K table fee hfee C accounting sample

/-- An unproved exact Native refinement target. Final D18 must discharge it
by actual run proofs; conditional assembly alone does not close D18. -/
def MenuNativeSummaryRefinement (P : Parameters) : Prop :=
  ∀ (N K : ℕ) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract (freshInstance N K)), C.IsCurrentPayment →
      ∀ accounting : NormalAccounting (freshInstance N K), MenuNativePathRecords P N K table fee hfee C accounting

def MenuEndpointFiniteSample (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World) : Prop :=
  ∀ (stage : (freshInstance N K).Stage) (level : ℕ) (coin : Bool), ∃ reviews : ℕ,
    (menuAnalysisTest P level).rule.stop coin
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews

theorem menuEndpointFiniteSample_ae (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee) :
    ∀ᵐ sample ∂(P.freshInput N K fee hfee).seededWorldLaw (menuSeedLaw N K),
      MenuEndpointFiniteSample P N K fee hfee sample :=
  menu_allEndpoints_finite_seededWorld P N K fee hfee (menuSeedLaw N K)

theorem menuNativePathRecords_of_finite_agreement (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K))
    (accounting : NormalAccounting (freshInstance N K))
    (hactual : ∀ sample, MenuEndpointFiniteSample P N K fee hfee sample →
      MenuNativePathAgreement P N K table fee hfee C accounting sample) :
    MenuNativePathRecords P N K table fee hfee C accounting := by
  filter_upwards [menuEndpointFiniteSample_ae P N K fee hfee] with sample hs
  exact hactual sample hs

end PDMenu
