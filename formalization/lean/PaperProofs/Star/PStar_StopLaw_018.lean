module

public import PaperProofs.Star.PStar_LocalWorld_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarStopLaw018

open Common Common.Native Statistics MeasureTheory PStarLocalWorld012
open scoped ENNReal

/-- Increasing the original error target can only decrease its actual
first threshold exit on the SAME tape, including infinite exits. -/
theorem realPosteriorStop_antitone (E : BinaryExperiment) (small large : ℝ)
    (positive : 0 < small) (ordered : small ≤ large) (half : large ≤ 1 / 2) (tape : E.Tape) :
    realPosteriorStop E large tape ≤ realPosteriorStop E small tape := by
  have largePositive : 0 < large := positive.trans_le ordered
  have ratio : (1-large)/large ≤ (1-small)/small := by
    apply (div_le_div_iff₀ largePositive positive).mpr
    nlinarith
  have threshold : Real.log ((1-large)/large) ≤ Real.log ((1-small)/small) :=
    Real.log_le_log (div_pos (by linarith) largePositive) ratio
  unfold realPosteriorStop
  apply le_sInf
  rintro exit ⟨n, rfl, hit⟩
  exact sInf_le ⟨n, rfl, threshold.trans hit⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem realPosteriorStop_world_ae (P : PaperProofs.Star.Parameters) (order : Order)
    (stage : (starInstance P.tools order).Stage) (target : ℝ)
    (positive : 0 < target) (half : target < 1/2) :
    ∀ᵐ sample : Unit × (P.input order).World ∂(P.input order).seededWorldLaw (Measure.dirac ()),
      realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 stage) ≠ ⊤ := by
  let test := P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel target)
  let charge : Unit × (P.input order).World → ℝ≥0∞ :=
    fun sample => localCharge (P.input order) stage test (sample.2 stage)
  have measurableCharge : Measurable charge :=
    (measurable_localCharge (P.input order) stage test).comp
      ((measurable_pi_apply stage).comp measurable_snd)
  have law := lintegral_localCoordinate (P.input order) stage
    (localCharge (P.input order) stage test) (measurable_localCharge (P.input order) stage test)
  have finite : (∫⁻ sample, charge sample ∂(P.input order).seededWorldLaw (Measure.dirac ())) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (law.le.trans (realTarget_localCharge_le P order stage target positive half))
  filter_upwards [ae_lt_top measurableCharge finite] with sample finiteCharge
  intro infinite
  have stop : test.rule.stop () ((P.input order).reviewAt sample.2 stage) = ⊤ :=
    (PStarLR.realPosteriorStop_eq_hitting P.channel target _).symm.trans infinite
  change P.channel.experiment.observationCharge
    (test.rule.stop () ((P.input order).reviewAt sample.2 stage)) < ⊤ at finiteCharge
  rw [stop, BinaryExperiment.observationCharge_top] at finiteCharge
  exact lt_irrefl _ finiteCharge

theorem all_realPosteriorStops_world_ae (P : PaperProofs.Star.Parameters) (order : Order)
    (target : ℝ) (positive : 0 < target) (half : target < 1/2) :
    ∀ᵐ sample : Unit × (P.input order).World ∂(P.input order).seededWorldLaw (Measure.dirac ()),
      ∀ stage : (starInstance P.tools order).Stage,
        realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 stage) ≠ ⊤ := by
  exact ae_all_iff.mpr (fun stage => realPosteriorStop_world_ae P order stage target positive half)

end PaperProofs.Star.PStarStopLaw018
