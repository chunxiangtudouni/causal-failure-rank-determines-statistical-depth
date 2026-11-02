module

public import PaperProofs.Paid.PDMenu_MenuPathMeasurable_089
public import PaperProofs.Common.NativeBellmanFiniteStop

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC.MenuExpected

abbrev Head (P : Parameters) := Bool × (Bool × P.experiment.Tape)

noncomputable def headLaw (P : Parameters) : Measure (Head P) :=
  PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw.prod (PDMenu.menuAnalysisStageLaw P)

instance headLaw_probability (P : Parameters) : IsProbabilityMeasure (headLaw P) := by
  unfold headLaw
  infer_instance

def correctGate (P : Parameters) (level : ℕ) : Set (Head P) :=
  BellmanExpectation.headCorrectGate (P.freshInput 1 0 0 (by decide)) PDMenu.menuAnalysisHead
    (PDMenu.menuAnalysisTest P level)

theorem measurableSet_correctGate (P : Parameters) (level : ℕ) : MeasurableSet (correctGate P level) :=
  BellmanExpectation.measurableSet_headCorrectGate _ _ _

noncomputable def headCharge (P : Parameters) (level : ℕ) (sample : Head P) : ℝ≥0∞ :=
  P.experiment.observationCharge ((PDMenu.menuAnalysisTest P level).rule.stop sample.1 sample.2.2)

theorem measurable_headCharge (P : Parameters) (level : ℕ) : Measurable (headCharge P level) :=
  (measurable_of_countable P.experiment.observationCharge).comp
    ((PDMenu.menuAnalysisTest P level).measurable_stop.comp
      (measurable_fst.prodMk measurable_snd.snd))

theorem correct_mass (P : Parameters) (level : ℕ) :
    headLaw P (correctGate P level) = ENNReal.ofReal (1-(P.binarySymmetric.endpointError level:ℝ)) :=
  PDMenu.freshEndpointTest_correctMass P 1 0 0 (by decide) PDMenu.menuAnalysisHead level

theorem wrong_mass (P : Parameters) (level : ℕ) :
    headLaw P (correctGate P level)ᶜ = ENNReal.ofReal (P.binarySymmetric.endpointError level:ℝ) := by
  have h := BellmanExpectation.wrongMass_eq_bayesError (P.freshInput 1 0 0 (by decide))
    PDMenu.menuAnalysisHead PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw
    (PDMenu.menuAnalysisTest P level)
  exact h.trans (PDMenu.menuAnalysisTest_bayesError P level)

theorem headCharge_integral (P : Parameters) (level : ℕ) :
    (∫⁻ sample, headCharge P level sample ∂headLaw P) =
      ENNReal.ofReal (P.binarySymmetric.endpointCharge level:ℝ) := by
  let input := P.freshInput 1 0 0 (by decide)
  let localLaw := PaperProofs.Statistics.BinarySymmetric.Parameters.fairGuessLaw
  let projection : Bool × input.World → Head P := fun sample => (sample.1,sample.2 PDMenu.menuAnalysisHead)
  have hm : Measurable projection := measurable_fst.prodMk
    ((measurable_pi_apply PDMenu.menuAnalysisHead).comp measurable_snd)
  have hmap : (input.seededWorldLaw localLaw).map projection = headLaw P :=
    BellmanExpectation.localHeadSeed_law input PDMenu.menuAnalysisHead localLaw
  have hp := lintegral_map (μ:=input.seededWorldLaw localLaw) (measurable_headCharge P level) hm
  rw [hmap] at hp
  have hb := bayesObservationCharge_eq_seededWorld_integral input PDMenu.menuAnalysisHead localLaw
    (PDMenu.menuAnalysisTest P level)
  exact hp.trans (hb.symm.trans (PDMenu.menuAnalysisTest_bayesCharge P level))

/-- Nonreturn is derived null on the original head law, including level zero.
The path-summary definition continues to retain its explicit infinite branch. -/
theorem head_stop_ae_finite (P : Parameters) (level : ℕ) :
    ∀ᵐ sample ∂headLaw P,
      (PDMenu.menuAnalysisTest P level).rule.stop sample.1 sample.2.2 ≠ ⊤ := by
  have hfinite : (∫⁻ sample, headCharge P level sample ∂headLaw P) ≠ ⊤ := by
    rw [headCharge_integral]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top (measurable_headCharge P level) hfinite] with sample hs
  intro htop
  simp only [headCharge, htop, PaperProofs.Statistics.BinaryExperiment.observationCharge_top,
    lt_self_iff_false] at hs

end PDROC.MenuExpected
