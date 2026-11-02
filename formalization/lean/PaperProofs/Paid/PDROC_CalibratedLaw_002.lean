module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_001
public import PaperProofs.Paid.PDROC_CalibratedLaw_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics
open scoped ENNReal

namespace PDROC.CalibratedLaw

open PDROC.CalibratedRuntime

noncomputable def markRowLaw (P : Parameters) : Measure (Fin (P.certificate.M + 1) → Bool) :=
  Measure.pi fun level => BinarySymmetric.Parameters.rocCoinLaw (P.clippedCalibrationWeight level.val)

instance markRowLaw_probability (P : Parameters) : IsProbabilityMeasure (markRowLaw P) := by
  unfold markRowLaw
  infer_instance

noncomputable def stageSeedLaw (P : Parameters) : Measure (StageSeed P) :=
  BinarySymmetric.Parameters.fairGuessLaw.prod (markRowLaw P)

instance stageSeedLaw_probability (P : Parameters) : IsProbabilityMeasure (stageSeedLaw P) := by
  unfold stageSeedLaw
  infer_instance

/-- The selected mark is read from the original independently sampled
whole level row; its fair bit is independent, and is never redrawn. -/
theorem localCalibrationSeed_law (P : Parameters) (level : ℕ) (valid : level ≤ P.certificate.M) :
    (stageSeedLaw P).map (localCalibrationSeed P level) = P.calibrationSeedLaw level := by
  let index : Fin (P.certificate.M + 1) := ⟨level, by omega⟩
  have hmark : (markRowLaw P).map (fun row => row index) =
      BinarySymmetric.Parameters.rocCoinLaw (P.clippedCalibrationWeight level) :=
    (measurePreserving_eval (fun i : Fin (P.certificate.M + 1) =>
      BinarySymmetric.Parameters.rocCoinLaw (P.clippedCalibrationWeight i.val)) index).map_eq
  have hprod := Measure.map_prod_map BinarySymmetric.Parameters.fairGuessLaw (markRowLaw P)
    measurable_id (measurable_pi_apply index)
  rw [Measure.map_id, hmark] at hprod
  have hswap := congrArg (fun μ => μ.map Prod.swap) hprod
  have hpair : Measurable (Prod.map (id : Bool → Bool)
      (fun row : Fin (P.certificate.M + 1) → Bool => row index)) :=
    (measurable_id : Measurable (id : Bool → Bool)).prodMap (measurable_pi_apply index)
  rw [Measure.prod_swap, Measure.map_map measurable_swap
    hpair] at hswap
  have hfun : localCalibrationSeed P level =
      (fun seed : StageSeed P => (seed.2 index, seed.1)) := by
    funext seed
    exact localCalibrationSeed_of_valid P level seed valid
  rw [hfun]
  change (BinarySymmetric.Parameters.fairGuessLaw.prod (markRowLaw P)).map
    (fun seed : StageSeed P => (seed.2 index, seed.1)) =
      (BinarySymmetric.Parameters.rocCoinLaw (P.clippedCalibrationWeight level)).prod
        BinarySymmetric.Parameters.fairGuessLaw
  simpa only [Function.comp_def, Prod.map, Prod.swap, id] using hswap.symm

noncomputable def analysisLaw (P : Parameters) (n : ℕ) :
    Measure ((Fin n → StageSeed P) × PDMenu.MenuAnalysisWorld P n) :=
  (Measure.pi fun _ : Fin n => stageSeedLaw P).prod
    (Measure.pi fun _ : Fin n => PDMenu.menuAnalysisStageLaw P)

instance analysisLaw_probability (P : Parameters) (n : ℕ) : IsProbabilityMeasure (analysisLaw P n) := by
  unfold analysisLaw
  infer_instance

def analysisSplit (P : Parameters) (n : ℕ)
    (sample : (Fin (n + 1) → StageSeed P) × PDMenu.MenuAnalysisWorld P (n + 1)) :
    (StageSeed P × (Bool × P.experiment.Tape)) × ((Fin n → StageSeed P) × PDMenu.MenuAnalysisWorld P n) :=
  ((sample.1 0, sample.2 0), (Fin.tail sample.1, Fin.tail sample.2))

theorem analysisSplit_measurePreserving (P : Parameters) (n : ℕ) :
    MeasurePreserving (analysisSplit P n) (analysisLaw P (n + 1))
      (((stageSeedLaw P).prod (PDMenu.menuAnalysisStageLaw P)).prod (analysisLaw P n)) := by
  have hs := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => stageSeedLaw P) 0
  have hw := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => PDMenu.menuAnalysisStageLaw P) 0
  have hshuffle := BellmanExpectation.measurePreserving_pairShuffle
    (stageSeedLaw P) (Measure.pi fun _ : Fin n => stageSeedLaw P)
    (PDMenu.menuAnalysisStageLaw P) (Measure.pi fun _ : Fin n => PDMenu.menuAnalysisStageLaw P)
  exact hshuffle.comp (hs.prod hw)

def calibrationMarksFinEquiv (P : Parameters) :
    P.CalibrationMarks ≃ᵐ (Fin P.certificate.stages → Fin (P.certificate.M + 1) → Bool) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin P.certificate.stages => Fin (P.certificate.M + 1) → Bool)
    (finCongr (by simp [Parameters.sharedInstance]))

theorem calibrationMarksFinEquiv_measurePreserving (P : Parameters) :
    MeasurePreserving (calibrationMarksFinEquiv P) P.calibrationMarksLaw
      (Measure.pi fun _ : Fin P.certificate.stages => markRowLaw P) :=
  measurePreserving_piCongrLeft (fun _ : Fin P.certificate.stages => markRowLaw P)
    (finCongr (by simp [Parameters.sharedInstance]))

/-- Rearrangement of the one original fixed whole seed, retaining every
potential level mark and the one fair bit at each physical stage. -/
def calibratedSeedFinView (P : Parameters) :
    P.CalibratedMenuSeed ≃ᵐ (Fin P.certificate.stages → StageSeed P) :=
  (((PDMenu.menuSeedFinEquiv P.certificate.stages P.tools).prodCongr
      (calibrationMarksFinEquiv P)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow Bool (Fin (P.certificate.M + 1) → Bool)
      (Fin P.certificate.stages)).symm)

theorem calibratedSeedFinView_apply (P : Parameters) (seed : P.CalibratedMenuSeed)
    (stage : Fin P.certificate.stages) :
    calibratedSeedFinView P seed stage =
      (seed.1 (PDMenu.menuStageAt P.certificate.stages P.tools stage),
       seed.2 (PDMenu.menuStageAt P.certificate.stages P.tools stage)) := rfl

theorem calibratedSeedFinView_measurePreserving (P : Parameters) :
    MeasurePreserving (calibratedSeedFinView P) P.calibratedMenuSeedLaw
      (Measure.pi fun _ : Fin P.certificate.stages => stageSeedLaw P) := by
  have hsplit := measurePreserving_arrowProdEquivProdArrow Bool (Fin (P.certificate.M + 1) → Bool)
    (Fin P.certificate.stages) (fun _ => BinarySymmetric.Parameters.fairGuessLaw) (fun _ => markRowLaw P)
  have hjoin := hsplit.symm
    (MeasurableEquiv.arrowProdEquivProdArrow Bool (Fin (P.certificate.M + 1) → Bool) (Fin P.certificate.stages))
  exact hjoin.comp ((PDMenu.menuSeedFinEquiv_measurePreserving P.certificate.stages P.tools).prod
    (calibrationMarksFinEquiv_measurePreserving P))

def calibratedSampleFinView (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    (P.CalibratedMenuSeed × (P.input fee hfee).World) ≃ᵐ
      ((Fin P.certificate.stages → StageSeed P) × PDMenu.MenuAnalysisWorld P P.certificate.stages) :=
  (calibratedSeedFinView P).prodCongr
    (PDMenu.menuWorldFinEquiv P P.certificate.stages P.tools fee hfee)

theorem calibratedSampleFinView_measurePreserving (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    MeasurePreserving (calibratedSampleFinView P fee hfee)
      ((P.input fee hfee).seededWorldLaw P.calibratedMenuSeedLaw) (analysisLaw P P.certificate.stages) :=
  (calibratedSeedFinView_measurePreserving P).prod
    (PDMenu.menuWorldFinEquiv_measurePreserving P P.certificate.stages P.tools fee hfee)

theorem calibratedSampleFinView_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    ((P.input fee hfee).seededWorldLaw P.calibratedMenuSeedLaw).map (calibratedSampleFinView P fee hfee) =
      analysisLaw P P.certificate.stages :=
  (calibratedSampleFinView_measurePreserving P fee hfee).map_eq

end PDROC.CalibratedLaw
