module

public import PaperProofs.Paid.PDMenu_MenuPathSummary_087
public import PaperProofs.Paid.PDMenu_MenuSeedSplit_071
public import PaperProofs.Common.NativeBellmanExpectation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Exactly the original single physical stage law, not a new channel. -/
noncomputable def menuAnalysisStageLaw (P : Parameters) : Measure (Bool × P.experiment.Tape) :=
  (P.freshInput 1 0 0 (by decide)).stageLaw menuAnalysisHead

instance menuAnalysisStageLaw_probability (P : Parameters) : IsProbabilityMeasure (menuAnalysisStageLaw P) := by
  exact StatisticalInput.stageLaw_probability (P.freshInput 1 0 0 (by decide)) menuAnalysisHead

noncomputable def menuAnalysisLaw (P : Parameters) (n : ℕ) :
    Measure (MenuAnalysisSeed n × MenuAnalysisWorld P n) :=
  (Measure.pi (fun _ : Fin n => PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw)).prod
    (Measure.pi (fun _ : Fin n => menuAnalysisStageLaw P))

instance menuAnalysisLaw_probability (P : Parameters) (n : ℕ) : IsProbabilityMeasure (menuAnalysisLaw P n) := by
  unfold menuAnalysisLaw
  infer_instance

def menuWorldFinEquiv (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee) :
    (P.freshInput N K fee hfee).World ≃ᵐ MenuAnalysisWorld P N :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin N => Bool × P.experiment.Tape)
    (finCongr (by simp [freshInstance]))

theorem menuWorldFinEquiv_apply (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (world : (P.freshInput N K fee hfee).World) (i : Fin N) :
    menuWorldFinEquiv P N K fee hfee world i = world (menuStageAt N K i) := rfl

theorem menuWorldFinEquiv_measurePreserving (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee) :
    MeasurePreserving (menuWorldFinEquiv P N K fee hfee) (P.freshInput N K fee hfee).worldLaw
      (Measure.pi (fun _ : Fin N => menuAnalysisStageLaw P)) :=
  measurePreserving_piCongrLeft (fun _ : Fin N => menuAnalysisStageLaw P) (finCongr (by simp [freshInstance]))

/-- Reindexing retains the original per-stage private bits and every truth
and complete potential tape, with the exact original joint probability law. -/
def menuSampleFinView (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee) :
    (MenuSeed N K × (P.freshInput N K fee hfee).World) ≃ᵐ (MenuAnalysisSeed N × MenuAnalysisWorld P N) :=
  (menuSeedFinEquiv N K).prodCongr (menuWorldFinEquiv P N K fee hfee)

theorem menuSampleFinView_measurePreserving (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee) :
    MeasurePreserving (menuSampleFinView P N K fee hfee)
      ((P.freshInput N K fee hfee).seededWorldLaw (menuSeedLaw N K)) (menuAnalysisLaw P N) :=
  (menuSeedFinEquiv_measurePreserving N K).prod (menuWorldFinEquiv_measurePreserving P N K fee hfee)

theorem menuSampleFinView_law (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee) :
    ((P.freshInput N K fee hfee).seededWorldLaw (menuSeedLaw N K)).map (menuSampleFinView P N K fee hfee) =
      menuAnalysisLaw P N := (menuSampleFinView_measurePreserving P N K fee hfee).map_eq

def menuAnalysisSplit (P : Parameters) (n : ℕ) (sample : MenuAnalysisSeed (n + 1) × MenuAnalysisWorld P (n + 1)) :
    (Bool × (Bool × P.experiment.Tape)) × (MenuAnalysisSeed n × MenuAnalysisWorld P n) :=
  ((sample.1 0, sample.2 0), (Fin.tail sample.1, Fin.tail sample.2))

theorem menuAnalysisSplit_measurePreserving (P : Parameters) (n : ℕ) :
    MeasurePreserving (menuAnalysisSplit P n) (menuAnalysisLaw P (n + 1))
      ((PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw.prod (menuAnalysisStageLaw P)).prod
        (menuAnalysisLaw P n)) := by
  have hs := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) =>
    PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw) 0
  have hw := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => menuAnalysisStageLaw P) 0
  have hsplit := hs.prod hw
  have hshuffle := BellmanExpectation.measurePreserving_pairShuffle
    PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw
    (Measure.pi (fun _ : Fin n => PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw))
    (menuAnalysisStageLaw P) (Measure.pi (fun _ : Fin n => menuAnalysisStageLaw P))
  exact hshuffle.comp hsplit

/-- A precise analysis target for the summary, not a supplied native Policy
performance field and not a theorem of the present definition module. -/
def MenuPathMeans (P : Parameters) (table : MenuTable) (n k : ℕ) : Prop :=
  (∫⁻ sample, (menuPathSummary P table n k sample.1 sample.2).observation ∂menuAnalysisLaw P n) =
      ENNReal.ofReal ((Parameters.menuEntryAt table n k).observation : ℝ) ∧
  (∫⁻ sample, ((menuPathSummary P table n k sample.1 sample.2).physicalRepairs : ℝ≥0∞) ∂menuAnalysisLaw P n) =
      ENNReal.ofReal ((Parameters.menuEntryAt table n k).repairs : ℝ) ∧
  (menuAnalysisLaw P n) {sample | (menuPathSummary P table n k sample.1 sample.2).failure = true} =
      ENNReal.ofReal ((Parameters.menuEntryAt table n k).failure : ℝ)

def ExpectedMenuPathRecords (P : Parameters) : Prop :=
  ∀ (fee penalty : ℚ) (N K n k : ℕ), n ≤ N → k ≤ K →
    MenuPathMeans P (P.solveMenuTable fee penalty K N) n k

end PDMenu
