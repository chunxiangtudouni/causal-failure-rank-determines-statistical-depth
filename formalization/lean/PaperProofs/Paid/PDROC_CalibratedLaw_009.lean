module

public import PaperProofs.Paid.PDROC_CalibratedLaw_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Statistics
open scoped ENNReal

namespace PDROC.CalibratedLaw

open PDROC.CalibratedRuntime

/-- The single shared summary evaluated on the original complete calibrated
seed and original complete world; this introduces no new sampling. -/
noncomputable def calibratedRawRecord (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World) : PathRecord :=
  let view := calibratedSampleFinView P fee hfee sample
  pathSummary P (calibratedFamily P) table P.certificate.stages P.tools view.1 view.2

/-- The same summary ABI evaluated on the original ideal menu seed/world. -/
noncomputable def idealRawRecord (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World) : PathRecord :=
  let view := PDMenu.menuSampleFinView P P.certificate.stages P.tools fee hfee sample
  pathSummary P (idealFamily P) table P.certificate.stages P.tools view.1 view.2

theorem measurable_calibratedRawRecord (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) :
    MeasurablePathRecord (calibratedRawRecord P table fee hfee) :=
  (measurable_pathSummary P (calibratedFamily P) table P.certificate.stages P.tools).comp
    (calibratedSampleFinView P fee hfee).measurable

theorem measurable_idealRawRecord (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) :
    MeasurablePathRecord (idealRawRecord P table fee hfee) :=
  (measurable_pathSummary P (idealFamily P) table P.certificate.stages P.tools).comp
    (PDMenu.menuSampleFinView P P.certificate.stages P.tools fee hfee).measurable

theorem calibratedRawRecord_outcome_law (P : Parameters) (table : MenuTable)
    (valid : TableLevelsValid P table) (fee : ℚ) (hfee : 0 ≤ fee) :
    ((P.input fee hfee).seededWorldLaw P.calibratedMenuSeedLaw).map
        (fun sample => (calibratedRawRecord P table fee hfee sample).outcome) =
      ((P.input fee hfee).seededWorldLaw (menuSeedLaw P.certificate.stages P.tools)).map
        (fun sample => (idealRawRecord P table fee hfee sample).outcome) := by
  have hc := congrArg
    (fun law => law.map (fun sample : TailOf P (StageSeed P) P.certificate.stages =>
      (pathSummary P (calibratedFamily P) table P.certificate.stages P.tools sample.1 sample.2).outcome))
    (calibratedSampleFinView_law P fee hfee)
  rw [Measure.map_map (measurable_pathOutcome P (calibratedFamily P) table _ _)
    (calibratedSampleFinView P fee hfee).measurable] at hc
  have hi := congrArg
    (fun law => law.map (fun sample : TailOf P Bool P.certificate.stages =>
      (pathSummary P (idealFamily P) table P.certificate.stages P.tools sample.1 sample.2).outcome))
    (PDMenu.menuSampleFinView_law P P.certificate.stages P.tools fee hfee)
  rw [Measure.map_map (measurable_pathOutcome P (idealFamily P) table _ _)
    (PDMenu.menuSampleFinView P P.certificate.stages P.tools fee hfee).measurable] at hi
  exact hc.trans ((pathOutcome_law P table valid P.certificate.stages P.tools).trans hi.symm)

theorem calibratedRawRecord_observation_le_four (P : Parameters) (table : MenuTable)
    (valid : TableLevelsValid P table) (fee : ℚ) (hfee : 0 ≤ fee) :
    (∫⁻ sample, (calibratedRawRecord P table fee hfee sample).observation
      ∂(P.input fee hfee).seededWorldLaw P.calibratedMenuSeedLaw) ≤
      4 * (∫⁻ sample, (idealRawRecord P table fee hfee sample).observation
        ∂(P.input fee hfee).seededWorldLaw (menuSeedLaw P.certificate.stages P.tools)) := by
  have hc := (calibratedSampleFinView_measurePreserving P fee hfee).lintegral_comp
    (measurable_pathObservation P (calibratedFamily P) table P.certificate.stages P.tools)
  have hi := (PDMenu.menuSampleFinView_measurePreserving P P.certificate.stages P.tools fee hfee).lintegral_comp
    (measurable_pathObservation P (idealFamily P) table P.certificate.stages P.tools)
  exact hc.trans_le ((pathObservation_integral_le_four P table valid P.certificate.stages P.tools).trans_eq
    (congrArg (fun value : ℝ≥0∞ => 4 * value) hi.symm))

theorem solveMenuTable_raw_outcome_law (P : Parameters) (fee penalty : ℚ)
    (hfee : 0 ≤ fee) :
    ((P.input fee hfee).seededWorldLaw P.calibratedMenuSeedLaw).map
        (fun sample => (calibratedRawRecord P
          (P.solveMenuTable fee penalty P.tools P.certificate.stages) fee hfee sample).outcome) =
      ((P.input fee hfee).seededWorldLaw (menuSeedLaw P.certificate.stages P.tools)).map
        (fun sample => (idealRawRecord P
          (P.solveMenuTable fee penalty P.tools P.certificate.stages) fee hfee sample).outcome) :=
  calibratedRawRecord_outcome_law P _
    (solveMenuTable_levelsValid P fee penalty P.certificate.stages P.tools) fee hfee

theorem solveMenuTable_raw_observation_le_four (P : Parameters) (fee penalty : ℚ)
    (hfee : 0 ≤ fee) :
    (∫⁻ sample, (calibratedRawRecord P
      (P.solveMenuTable fee penalty P.tools P.certificate.stages) fee hfee sample).observation
      ∂(P.input fee hfee).seededWorldLaw P.calibratedMenuSeedLaw) ≤
      4 * (∫⁻ sample, (idealRawRecord P
        (P.solveMenuTable fee penalty P.tools P.certificate.stages) fee hfee sample).observation
        ∂(P.input fee hfee).seededWorldLaw (menuSeedLaw P.certificate.stages P.tools)) :=
  calibratedRawRecord_observation_le_four P _
    (solveMenuTable_levelsValid P fee penalty P.certificate.stages P.tools) fee hfee

end PDROC.CalibratedLaw
