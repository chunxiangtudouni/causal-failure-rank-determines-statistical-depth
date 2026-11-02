module

public import PaperProofs.Paid.PDROC_Simulator_010
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

/-- Remove exactly the current coordinate from a finite independent family.
The complement can include all earlier and all later coordinates. -/
theorem pi_other_current_jointLaw {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (current : ι) :
    (Measure.pi (fun _ : ι => μ)).map (fun values =>
      ((fun other : {i : ι // i ≠ current} => values other.val), values current)) =
      (Measure.pi (fun _ : {i : ι // i ≠ current} => μ)).prod μ := by
  classical
  let split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => α) (fun i => i ≠ current)
  let pick : (({i : ι // i ≠ current} → α) × ({i : ι // ¬ i ≠ current} → α)) →
      (({i : ι // i ≠ current} → α) × α) := Prod.map id (Function.eval ⟨current, by simp⟩)
  have hsplit := (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ≠ current)).map_eq
  have hpick : Measurable pick := measurable_id.prodMap (measurable_pi_apply (⟨current, by simp⟩ : {i : ι // ¬ i ≠ current}))
  have h := congrArg (fun ρ => ρ.map pick) hsplit
  rw [Measure.map_map hpick split.measurable,
    ← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply (⟨current, by simp⟩ : {i : ι // ¬ i ≠ current})),
    Measure.map_id, (measurePreserving_eval (fun _ : {i : ι // ¬ i ≠ current} => μ) ⟨current, by simp⟩).map_eq] at h
  exact h

/-- Exchange the middle two factors of four genuinely independent laws. -/
theorem product_exchange_jointLaw {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μA : Measure A) (μB : Measure B) (μC : Measure C) (μD : Measure D)
    [IsProbabilityMeasure μA] [IsProbabilityMeasure μB] [IsProbabilityMeasure μC] [IsProbabilityMeasure μD] :
    ((μA.prod μB).prod (μC.prod μD)).map (fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))) =
      (μA.prod μC).prod (μB.prod μD) := by
  have h1 := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h2 := (MeasurePreserving.id μA).prod ((measurePreserving_prodAssoc μB μC μD).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ := μB) (ν := μC)).prod (MeasurePreserving.id μD))
  have h4 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h5 := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm MeasurableEquiv.prodAssoc
  exact (h5.comp (h4.comp (h3.comp (h2.comp h1)))).map_eq

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

abbrev SimulatorOtherNoise (P : PaperProofs.Paid.Parameters) (stage : P.sharedInstance.Stage) :=
  ({i : P.sharedInstance.Stage // i ≠ stage} → P.experiment.Tape) ×
    ({i : P.sharedInstance.Stage // i ≠ stage} → Bool)

def simulatorOtherNoise (P : PaperProofs.Paid.Parameters) (stage : P.sharedInstance.Stage)
    (seed : SimulatorSeed P Seed) : SimulatorOtherNoise P stage :=
  ((fun i => seed.2.1 i.val), fun i => seed.2.2 i.val)

def simulatorCurrentNoise (P : PaperProofs.Paid.Parameters) (stage : P.sharedInstance.Stage)
    (seed : SimulatorSeed P Seed) : P.experiment.Tape × Bool := (seed.2.1 stage, seed.2.2 stage)

noncomputable def simulatorOtherNoiseLaw (P : PaperProofs.Paid.Parameters) (stage : P.sharedInstance.Stage) :
    Measure (SimulatorOtherNoise P stage) :=
  (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => auxiliaryTapeLaw P)).prod
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => fairGuessLaw))

instance simulatorOtherNoiseLaw_probability (P : PaperProofs.Paid.Parameters) (stage : P.sharedInstance.Stage) :
    IsProbabilityMeasure (simulatorOtherNoiseLaw P stage) := by
  unfold simulatorOtherNoiseLaw
  change IsProbabilityMeasure ((Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => auxiliaryTapeLaw P)).prod
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => fairGuessLaw)))
  infer_instance




theorem simulatorNoise_other_current_jointLaw (P : PaperProofs.Paid.Parameters) (stage : P.sharedInstance.Stage) :
    ((simulatorAuxiliaryLaw P).prod (simulatorCoinLaw P)).map (fun noise =>
      (((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => noise.1 i.val),
        (fun i : {i : P.sharedInstance.Stage // i ≠ stage} => noise.2 i.val)), (noise.1 stage, noise.2 stage))) =
      (simulatorOtherNoiseLaw P stage).prod ((auxiliaryTapeLaw P).prod fairGuessLaw) := by
  let splitA := fun values : P.sharedInstance.Stage → P.experiment.Tape =>
    ((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => values i.val), values stage)
  let splitB := fun values : P.sharedInstance.Stage → Bool =>
    ((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => values i.val), values stage)
  have ha : Measurable splitA := (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)).prodMk (measurable_pi_apply stage)
  have hb : Measurable splitB := (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)).prodMk (measurable_pi_apply stage)
  have hA : (simulatorAuxiliaryLaw P).map splitA =
      (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => auxiliaryTapeLaw P)).prod (auxiliaryTapeLaw P) :=
    pi_other_current_jointLaw (auxiliaryTapeLaw P) stage
  have hB : (simulatorCoinLaw P).map splitB =
      (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => fairGuessLaw)).prod fairGuessLaw :=
    pi_other_current_jointLaw fairGuessLaw stage
  let exchange := fun x : ((({i : P.sharedInstance.Stage // i ≠ stage} → P.experiment.Tape) × P.experiment.Tape) ×
      (({i : P.sharedInstance.Stage // i ≠ stage} → Bool) × Bool)) => ((x.1.1, x.2.1), (x.1.2, x.2.2))
  have hx : Measurable exchange := by fun_prop
  have hmap := Measure.map_prod_map (simulatorAuxiliaryLaw P) (simulatorCoinLaw P) ha hb
  rw [hA, hB] at hmap
  have h := congrArg (fun ρ => ρ.map exchange) hmap.symm
  rw [Measure.map_map hx (ha.prodMap hb)] at h
  exact h.trans (product_exchange_jointLaw
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => auxiliaryTapeLaw P)) (auxiliaryTapeLaw P)
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => fairGuessLaw)) fairGuessLaw)

theorem simulatorSeedLaw_other_current_jointLaw (P : PaperProofs.Paid.Parameters) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    (simulatorSeedLaw P ν).map (fun seed =>
      ((seed.1, simulatorOtherNoise P stage seed), simulatorCurrentNoise P stage seed)) =
      (ν.prod (simulatorOtherNoiseLaw P stage)).prod ((auxiliaryTapeLaw P).prod fairGuessLaw) := by
  let split := fun noise : (P.sharedInstance.Stage → P.experiment.Tape) × (P.sharedInstance.Stage → Bool) =>
    (((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => noise.1 i.val),
      (fun i : {i : P.sharedInstance.Stage // i ≠ stage} => noise.2 i.val)), (noise.1 stage, noise.2 stage))
  have hs : Measurable split := by
    exact ((measurable_pi_iff.mpr fun i => (measurable_pi_apply i.val).comp measurable_fst).prodMk
      (measurable_pi_iff.mpr fun i => (measurable_pi_apply i.val).comp measurable_snd)).prodMk
      (((measurable_pi_apply stage).comp measurable_fst).prodMk ((measurable_pi_apply stage).comp measurable_snd))
  have hmap := Measure.map_prod_map ν ((simulatorAuxiliaryLaw P).prod (simulatorCoinLaw P)) measurable_id hs
  rw [Measure.map_id, simulatorNoise_other_current_jointLaw] at hmap
  have h := congrArg (fun ρ => ρ.map MeasurableEquiv.prodAssoc.symm) hmap.symm
  rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (measurable_id.prodMap hs)] at h
  exact h.trans (((measurePreserving_prodAssoc ν (simulatorOtherNoiseLaw P stage)
    ((auxiliaryTapeLaw P).prod fairGuessLaw)).symm MeasurableEquiv.prodAssoc).map_eq)

/-- An arbitrary independent external coordinate (in particular the entire
original actual world) can be retained with the source and all other noise. -/
theorem product_rotate_jointLaw {A B W : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace W]
    (μA : Measure A) (μB : Measure B) (μW : Measure W)
    [IsProbabilityMeasure μA] [IsProbabilityMeasure μB] [IsProbabilityMeasure μW] :
    ((μA.prod μB).prod μW).map (fun x => ((x.1.1, x.2), x.1.2)) = (μA.prod μW).prod μB := by
  have h1 := measurePreserving_prodAssoc μA μB μW
  have h2 := (MeasurePreserving.id μA).prod (Measure.measurePreserving_swap (μ := μB) (ν := μW))
  have h3 := (measurePreserving_prodAssoc μA μW μB).symm MeasurableEquiv.prodAssoc
  exact (h3.comp (h2.comp h1)).map_eq





abbrev SimulatorOtherWorld (P : PaperProofs.Paid.Parameters) (stage : P.sharedInstance.Stage) :=
  {i : P.sharedInstance.Stage // i ≠ stage} → Bool × P.experiment.Tape

def simulatorAllOther (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :
    (Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage :=
  ((sample.1.1, simulatorOtherNoise P stage sample.1), fun i => sample.2 i.val)

def simulatorFreshStage (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :
    (P.experiment.Tape × Bool) × (Bool × P.experiment.Tape) :=
  (simulatorCurrentNoise P stage sample.1, sample.2 stage)

noncomputable def simulatorAllOtherLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) (stage : P.sharedInstance.Stage) :
    Measure ((Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage) :=
  (ν.prod (simulatorOtherNoiseLaw P stage)).prod
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => (P.input fee hfee).stageLaw stage))

instance simulatorAllOtherLaw_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    IsProbabilityMeasure (simulatorAllOtherLaw P fee hfee ν stage) := by
  unfold simulatorAllOtherLaw
  change IsProbabilityMeasure ((ν.prod (simulatorOtherNoiseLaw P stage)).prod
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => (P.input fee hfee).stageLaw stage)))
  infer_instance

/-- Exact current auxiliary-tape/coin/actual-stage law independent of the
ORIGINAL source seed and every other auxiliary/coin/actual-world coordinate.
The actual hidden stage is a world coordinate, never private seed data. -/
theorem simulatorWorldLaw_allOther_freshStage (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (simulatorAllOther P fee hfee stage sample, simulatorFreshStage P fee hfee stage sample)) =
      (simulatorAllOtherLaw P fee hfee ν stage).prod
        (((auxiliaryTapeLaw P).prod fairGuessLaw).prod ((P.input fee hfee).stageLaw stage)) := by
  let splitSeed := fun seed : SimulatorSeed P Seed =>
    ((seed.1, simulatorOtherNoise P stage seed), simulatorCurrentNoise P stage seed)
  let splitWorld := fun world : (P.input fee hfee).World =>
    ((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => world i.val), world stage)
  have hs : Measurable splitSeed := by
    exact (measurable_fst.prodMk
      ((measurable_pi_iff.mpr fun i => (measurable_pi_apply i.val).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_pi_iff.mpr fun i => (measurable_pi_apply i.val).comp (measurable_snd.comp measurable_snd)))).prodMk
      (((measurable_pi_apply stage).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_pi_apply stage).comp (measurable_snd.comp measurable_snd)))
  have hw : Measurable splitWorld := (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val).prodMk (measurable_pi_apply stage)
  have hseed := simulatorSeedLaw_other_current_jointLaw P ν stage
  have hworld : (P.input fee hfee).worldLaw.map splitWorld =
      (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => (P.input fee hfee).stageLaw stage)).prod
        ((P.input fee hfee).stageLaw stage) :=
    pi_other_current_jointLaw ((P.input fee hfee).stageLaw stage) stage
  have hmap := Measure.map_prod_map (simulatorSeedLaw P ν) (P.input fee hfee).worldLaw hs hw
  rw [hseed, hworld] at hmap
  let exchange := fun x : (((Seed × SimulatorOtherNoise P stage) × (P.experiment.Tape × Bool)) ×
      (SimulatorOtherWorld P stage × (Bool × P.experiment.Tape))) => ((x.1.1, x.2.1), (x.1.2, x.2.2))
  have hx : Measurable exchange := by fun_prop
  have h := congrArg (fun ρ => ρ.map exchange) hmap.symm
  have hcomp := Measure.map_map (μ := (simulatorSeedLaw P ν).prod (P.input fee hfee).worldLaw) hx (hs.prodMap hw)
  exact hcomp.symm.trans (h.trans (product_exchange_jointLaw (ν.prod (simulatorOtherNoiseLaw P stage))
    ((auxiliaryTapeLaw P).prod fairGuessLaw)
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => (P.input fee hfee).stageLaw stage))
    ((P.input fee hfee).stageLaw stage)))

/-- Retain an arbitrary measurable generated-past object with the old seed;
its exact law stays product with the genuine fresh stage coordinates. -/
theorem simulatorWorldLaw_pastGate_freshStage {Past : Type*} [MeasurableSpace Past]
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (gate : ((Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage) → Past)
    (hg : Measurable gate) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (gate (simulatorAllOther P fee hfee stage sample), simulatorFreshStage P fee hfee stage sample)) =
      ((simulatorAllOtherLaw P fee hfee ν stage).map gate).prod
        (((auxiliaryTapeLaw P).prod fairGuessLaw).prod ((P.input fee hfee).stageLaw stage)) := by
  have hp : Measurable (Prod.map gate (id : (P.experiment.Tape × Bool) × (Bool × P.experiment.Tape) → _)) := hg.prodMap measurable_id
  have hs : Measurable (fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
      (simulatorAllOther P fee hfee stage sample, simulatorFreshStage P fee hfee stage sample)) := by
    unfold simulatorAllOther simulatorFreshStage simulatorOtherNoise simulatorCurrentNoise
    fun_prop
  have h := congrArg (fun ρ => ρ.map (Prod.map gate id)) (simulatorWorldLaw_allOther_freshStage P fee hfee ν stage)
  rw [Measure.map_map hp hs] at h
  have hprod := Measure.map_prod_map (simulatorAllOtherLaw P fee hfee ν stage)
    (((auxiliaryTapeLaw P).prod fairGuessLaw).prod ((P.input fee hfee).stageLaw stage)) hg measurable_id
  rw [Measure.map_id] at hprod
  exact h.trans hprod.symm





def simulatorRecordBase (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :
    ((Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage) × P.experiment.Tape :=
  (simulatorAllOther P fee hfee stage sample, sample.1.2.1 stage)

def simulatorFreshEndpoint (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :
    Bool × (Bool × P.experiment.Tape) := (sample.1.2.2 stage, sample.2 stage)

/-- The current auxiliary tape may enter the selected source record gate,
but the current endpoint coin and actual truth/tape remain a fresh product.
In particular this does NOT condition on the whole new private seed. -/
theorem simulatorWorldLaw_recordBase_freshEndpoint (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (simulatorRecordBase P fee hfee stage sample, simulatorFreshEndpoint P fee hfee stage sample)) =
      ((simulatorAllOtherLaw P fee hfee ν stage).prod (auxiliaryTapeLaw P)).prod
        (fairGuessLaw.prod ((P.input fee hfee).stageLaw stage)) := by
  let split := fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
    (simulatorAllOther P fee hfee stage sample, simulatorFreshStage P fee hfee stage sample)
  have hs : Measurable split := by
    unfold split simulatorAllOther simulatorFreshStage simulatorOtherNoise simulatorCurrentNoise
    fun_prop
  have hsplit : MeasurePreserving split ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν))
      ((simulatorAllOtherLaw P fee hfee ν stage).prod
        (((auxiliaryTapeLaw P).prod fairGuessLaw).prod ((P.input fee hfee).stageLaw stage))) :=
    ⟨hs, simulatorWorldLaw_allOther_freshStage P fee hfee ν stage⟩
  have h1 := (MeasurePreserving.id (simulatorAllOtherLaw P fee hfee ν stage)).prod
    (measurePreserving_prodAssoc (auxiliaryTapeLaw P) fairGuessLaw ((P.input fee hfee).stageLaw stage))
  have h2 := (measurePreserving_prodAssoc (simulatorAllOtherLaw P fee hfee ν stage)
    (auxiliaryTapeLaw P) (fairGuessLaw.prod ((P.input fee hfee).stageLaw stage))).symm MeasurableEquiv.prodAssoc
  exact ((h2.comp h1).comp hsplit).map_eq

theorem simulatorWorldLaw_recordGate_freshEndpoint {RecordGate : Type*} [MeasurableSpace RecordGate]
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (gate : (((Seed × SimulatorOtherNoise P stage) × SimulatorOtherWorld P stage) × P.experiment.Tape) → RecordGate)
    (hg : Measurable gate) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (gate (simulatorRecordBase P fee hfee stage sample), simulatorFreshEndpoint P fee hfee stage sample)) =
      (((simulatorAllOtherLaw P fee hfee ν stage).prod (auxiliaryTapeLaw P)).map gate).prod
        (fairGuessLaw.prod ((P.input fee hfee).stageLaw stage)) := by
  have hp : Measurable (Prod.map gate (id : Bool × (Bool × P.experiment.Tape) → _)) := hg.prodMap measurable_id
  have hs : Measurable (fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
      (simulatorRecordBase P fee hfee stage sample, simulatorFreshEndpoint P fee hfee stage sample)) := by
    unfold simulatorRecordBase simulatorFreshEndpoint simulatorAllOther simulatorOtherNoise
    fun_prop
  have h := congrArg (fun ρ => ρ.map (Prod.map gate id)) (simulatorWorldLaw_recordBase_freshEndpoint P fee hfee ν stage)
  have hc := Measure.map_map (μ := (P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)) hp hs
  have hprod := Measure.map_prod_map ((simulatorAllOtherLaw P fee hfee ν stage).prod (auxiliaryTapeLaw P))
    (fairGuessLaw.prod ((P.input fee hfee).stageLaw stage)) hg measurable_id
  rw [Measure.map_id] at hprod
  exact hc.symm.trans (h.trans hprod.symm)

end PDROC
