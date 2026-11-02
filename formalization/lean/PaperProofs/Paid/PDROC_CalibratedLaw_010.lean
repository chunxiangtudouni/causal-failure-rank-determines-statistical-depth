module

public import PaperProofs.Paid.PDROC_CalibratedLaw_009
public import PaperProofs.Paid.PDROC_CalibratedSignature_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Statistics
open scoped ENNReal

namespace PDROC.CalibratedLaw

open PDROC.CalibratedRuntime

/-- One original initial bit chooses a whole stored table for the run. -/
noncomputable def calibratedSelectedRecord (P : Parameters) (tableOf : Bool → MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee)
    (sample : (Bool × P.CalibratedMenuSeed) × (P.input fee hfee).World) : PathRecord :=
  calibratedRawRecord P (tableOf sample.1.1) fee hfee (sample.1.2, sample.2)

noncomputable def idealSelectedRecord (P : Parameters) (tableOf : Bool → MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee)
    (sample : (Bool × MenuSeed P.certificate.stages P.tools) × (P.input fee hfee).World) : PathRecord :=
  idealRawRecord P (tableOf sample.1.1) fee hfee (sample.1.2, sample.2)

theorem measurable_calibratedSelectedRecord (P : Parameters) (tableOf : Bool → MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) :
    MeasurablePathRecord (calibratedSelectedRecord P tableOf fee hfee) := by
  constructor
  · exact PDROC.CalibratedSignature.measurable_initialSelector
      (fun branch sample => (calibratedRawRecord P (tableOf branch) fee hfee sample).observation)
      (fun branch => (measurable_calibratedRawRecord P (tableOf branch) fee hfee).1)
  · exact PDROC.CalibratedSignature.measurable_initialSelector
      (fun branch sample => (calibratedRawRecord P (tableOf branch) fee hfee sample).outcome)
      (fun branch => (measurable_calibratedRawRecord P (tableOf branch) fee hfee).2)

theorem measurable_idealSelectedRecord (P : Parameters) (tableOf : Bool → MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) :
    MeasurablePathRecord (idealSelectedRecord P tableOf fee hfee) := by
  constructor
  · exact PDROC.CalibratedSignature.measurable_initialSelector
      (fun branch sample => (idealRawRecord P (tableOf branch) fee hfee sample).observation)
      (fun branch => (measurable_idealRawRecord P (tableOf branch) fee hfee).1)
  · exact PDROC.CalibratedSignature.measurable_initialSelector
      (fun branch sample => (idealRawRecord P (tableOf branch) fee hfee sample).outcome)
      (fun branch => (measurable_idealRawRecord P (tableOf branch) fee hfee).2)

theorem calibratedSelectedRecord_outcome_law (P : Parameters) (tableOf : Bool → MenuTable)
    (valid : ∀ branch, TableLevelsValid P (tableOf branch))
    (weight : Set.Icc (0 : ℝ) 1) (fee : ℚ) (hfee : 0 ≤ fee) :
    ((P.input fee hfee).seededWorldLaw
      ((BinarySymmetric.Parameters.rocCoinLaw weight).prod P.calibratedMenuSeedLaw)).map
        (fun sample => (calibratedSelectedRecord P tableOf fee hfee sample).outcome) =
      ((P.input fee hfee).seededWorldLaw
        ((BinarySymmetric.Parameters.rocCoinLaw weight).prod
          (menuSeedLaw P.certificate.stages P.tools))).map
        (fun sample => (idealSelectedRecord P tableOf fee hfee sample).outcome) := by
  have hc := PDROC.CalibratedSignature.initialSelector_map P.calibratedMenuSeedLaw
    (P.input fee hfee).worldLaw weight
    (fun branch sample => (calibratedRawRecord P (tableOf branch) fee hfee sample).outcome)
    (fun branch => (measurable_calibratedRawRecord P (tableOf branch) fee hfee).2)
  have hi := PDROC.CalibratedSignature.initialSelector_map
    (menuSeedLaw P.certificate.stages P.tools) (P.input fee hfee).worldLaw weight
    (fun branch sample => (idealRawRecord P (tableOf branch) fee hfee sample).outcome)
    (fun branch => (measurable_idealRawRecord P (tableOf branch) fee hfee).2)
  rw [show ((P.input fee hfee).seededWorldLaw
      ((BinarySymmetric.Parameters.rocCoinLaw weight).prod P.calibratedMenuSeedLaw)).map
        (fun sample => (calibratedSelectedRecord P tableOf fee hfee sample).outcome) = _ from hc]
  rw [show ((P.input fee hfee).seededWorldLaw
      ((BinarySymmetric.Parameters.rocCoinLaw weight).prod (menuSeedLaw P.certificate.stages P.tools))).map
        (fun sample => (idealSelectedRecord P tableOf fee hfee sample).outcome) = _ from hi]
  exact congrArg₂ (fun (yes no : Measure Outcome) =>
      ENNReal.ofReal weight.val • yes + ENNReal.ofReal (1 - weight.val) • no)
    (calibratedRawRecord_outcome_law P (tableOf true) (valid true) fee hfee)
    (calibratedRawRecord_outcome_law P (tableOf false) (valid false) fee hfee)

theorem calibratedSelectedRecord_observation_le_four (P : Parameters) (tableOf : Bool → MenuTable)
    (valid : ∀ branch, TableLevelsValid P (tableOf branch))
    (weight : Set.Icc (0 : ℝ) 1) (fee : ℚ) (hfee : 0 ≤ fee) :
    (∫⁻ sample, (calibratedSelectedRecord P tableOf fee hfee sample).observation
      ∂(P.input fee hfee).seededWorldLaw
        ((BinarySymmetric.Parameters.rocCoinLaw weight).prod P.calibratedMenuSeedLaw)) ≤
      4 * (∫⁻ sample, (idealSelectedRecord P tableOf fee hfee sample).observation
        ∂(P.input fee hfee).seededWorldLaw
          ((BinarySymmetric.Parameters.rocCoinLaw weight).prod (menuSeedLaw P.certificate.stages P.tools))) := by
  have hc := PDROC.CalibratedSignature.lintegral_initialSelector P.calibratedMenuSeedLaw
    (P.input fee hfee).worldLaw weight
    (fun branch sample => (calibratedRawRecord P (tableOf branch) fee hfee sample).observation)
    (fun branch => (measurable_calibratedRawRecord P (tableOf branch) fee hfee).1)
  have hi := PDROC.CalibratedSignature.lintegral_initialSelector
    (menuSeedLaw P.certificate.stages P.tools) (P.input fee hfee).worldLaw weight
    (fun branch sample => (idealRawRecord P (tableOf branch) fee hfee sample).observation)
    (fun branch => (measurable_idealRawRecord P (tableOf branch) fee hfee).1)
  change (∫⁻ sample, (calibratedSelectedRecord P tableOf fee hfee sample).observation
    ∂(P.input fee hfee).seededWorldLaw
      ((BinarySymmetric.Parameters.rocCoinLaw weight).prod P.calibratedMenuSeedLaw)) = _ at hc
  change (∫⁻ sample, (idealSelectedRecord P tableOf fee hfee sample).observation
    ∂(P.input fee hfee).seededWorldLaw
      ((BinarySymmetric.Parameters.rocCoinLaw weight).prod (menuSeedLaw P.certificate.stages P.tools))) = _ at hi
  rw [hc, hi]
  calc
    _ ≤ ENNReal.ofReal weight.val * (4 * (∫⁻ sample,
          (idealRawRecord P (tableOf true) fee hfee sample).observation
          ∂(P.input fee hfee).seededWorldLaw (menuSeedLaw P.certificate.stages P.tools))) +
        ENNReal.ofReal (1 - weight.val) * (4 * (∫⁻ sample,
          (idealRawRecord P (tableOf false) fee hfee sample).observation
          ∂(P.input fee hfee).seededWorldLaw (menuSeedLaw P.certificate.stages P.tools))) :=
      add_le_add
        (mul_le_mul' le_rfl (calibratedRawRecord_observation_le_four P (tableOf true) (valid true) fee hfee))
        (mul_le_mul' le_rfl (calibratedRawRecord_observation_le_four P (tableOf false) (valid false) fee hfee))
    _ = _ := by rw [mul_add]; ac_rfl

end PDROC.CalibratedLaw
