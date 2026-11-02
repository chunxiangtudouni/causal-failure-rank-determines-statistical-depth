module

public import PaperProofs.Paid.PDROC_Simulator_004
public import PaperProofs.Paid.PDROC_LocalRecord_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- All stage auxiliary tapes are drawn directly from the fair tape mixture.
No latent fact, future truth, or completed source trace is a seed coordinate. -/
noncomputable def simulatorAuxiliaryLaw (P : PaperProofs.Paid.Parameters) :
    Measure (P.sharedInstance.Stage → P.experiment.Tape) :=
  Measure.pi (fun _ : P.sharedInstance.Stage => auxiliaryTapeLaw P)

instance simulatorAuxiliaryLaw_probability (P : PaperProofs.Paid.Parameters) :
    IsProbabilityMeasure (simulatorAuxiliaryLaw P) := by
  unfold simulatorAuxiliaryLaw
  change IsProbabilityMeasure (Measure.pi (fun _ : P.sharedInstance.Stage => auxiliaryTapeLaw P))
  infer_instance

noncomputable def simulatorCoinLaw (P : PaperProofs.Paid.Parameters) :
    Measure (P.sharedInstance.Stage → Bool) :=
  Measure.pi (fun _ : P.sharedInstance.Stage => fairGuessLaw)

instance simulatorCoinLaw_probability (P : PaperProofs.Paid.Parameters) :
    IsProbabilityMeasure (simulatorCoinLaw P) := by
  unfold simulatorCoinLaw
  infer_instance

noncomputable def simulatorSeedLaw (P : PaperProofs.Paid.Parameters) (ν : Measure Seed) :
    Measure (SimulatorSeed P Seed) :=
  ν.prod ((simulatorAuxiliaryLaw P).prod (simulatorCoinLaw P))

instance simulatorSeedLaw_probability (P : PaperProofs.Paid.Parameters) (ν : Measure Seed)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (simulatorSeedLaw P ν) := by
  unfold simulatorSeedLaw
  infer_instance

theorem simulatorSeedLaw_source (P : PaperProofs.Paid.Parameters) (ν : Measure Seed) [SFinite ν] :
    (simulatorSeedLaw P ν).map (fun seed => seed.1) = ν := by
  simp only [simulatorSeedLaw, Measure.map_fst_prod, measure_univ, one_smul]

theorem simulatorSeedLaw_auxiliary (P : PaperProofs.Paid.Parameters) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    (simulatorSeedLaw P ν).map (fun seed => seed.2.1) = simulatorAuxiliaryLaw P := by
  rw [show (fun seed : SimulatorSeed P Seed => seed.2.1) = Prod.fst ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_fst measurable_snd]
  simp only [simulatorSeedLaw, Measure.map_snd_prod, measure_univ, one_smul, Measure.map_fst_prod]

theorem simulatorSeedLaw_coins (P : PaperProofs.Paid.Parameters) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    (simulatorSeedLaw P ν).map (fun seed => seed.2.2) = simulatorCoinLaw P := by
  rw [show (fun seed : SimulatorSeed P Seed => seed.2.2) = Prod.snd ∘ Prod.snd from rfl,
    ← Measure.map_map measurable_snd measurable_snd]
  simp only [simulatorSeedLaw, Measure.map_snd_prod, measure_univ, one_smul]

theorem simulatorAuxiliaryLaw_eval (P : PaperProofs.Paid.Parameters) (stage : P.sharedInstance.Stage) :
    (simulatorAuxiliaryLaw P).map (Function.eval stage) = auxiliaryTapeLaw P :=
  (measurePreserving_eval (fun _ : P.sharedInstance.Stage => auxiliaryTapeLaw P) stage).map_eq

theorem simulatorCoinLaw_eval (P : PaperProofs.Paid.Parameters) (stage : P.sharedInstance.Stage) :
    (simulatorCoinLaw P).map (Function.eval stage) = fairGuessLaw :=
  (measurePreserving_eval (fun _ : P.sharedInstance.Stage => fairGuessLaw) stage).map_eq

theorem simulatorSeedLaw_auxiliary_eval (P : PaperProofs.Paid.Parameters) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    (simulatorSeedLaw P ν).map (fun seed => seed.2.1 stage) = auxiliaryTapeLaw P := by
  have hp : Measurable (fun seed : SimulatorSeed P Seed => seed.2.1) := measurable_fst.comp measurable_snd
  have he : Measurable (Function.eval stage : (P.sharedInstance.Stage → P.experiment.Tape) → P.experiment.Tape) :=
    measurable_pi_apply stage
  have h := Measure.map_map (μ := simulatorSeedLaw P ν) he hp
  exact h.symm.trans ((congrArg (fun ρ : Measure (P.sharedInstance.Stage → P.experiment.Tape) =>
    ρ.map (Function.eval stage)) (simulatorSeedLaw_auxiliary P ν)).trans (simulatorAuxiliaryLaw_eval P stage))

theorem simulatorSeedLaw_endpointCoin_eval (P : PaperProofs.Paid.Parameters) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    (simulatorSeedLaw P ν).map (fun seed => seed.2.2 stage) = fairGuessLaw := by
  have hp : Measurable (fun seed : SimulatorSeed P Seed => seed.2.2) := measurable_snd.comp measurable_snd
  have he : Measurable (Function.eval stage : (P.sharedInstance.Stage → Bool) → Bool) := measurable_pi_apply stage
  have h := Measure.map_map (μ := simulatorSeedLaw P ν) he hp
  exact h.symm.trans ((congrArg (fun ρ : Measure (P.sharedInstance.Stage → Bool) =>
    ρ.map (Function.eval stage)) (simulatorSeedLaw_coins P ν)).trans (simulatorCoinLaw_eval P stage))

end PDROC
