module

public import PaperProofs.Paid.PDROC_OverlayFresh_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v
variable {Seed : Type u} {Row : Type v} [MeasurableSpace Seed] [MeasurableSpace Row]

abbrev OverlayFullOtherNoise (P : Parameters) (Row : Type v) (stage : P.sharedInstance.Stage) :=
  ({i : P.sharedInstance.Stage // i ≠ stage} → P.experiment.Tape) ×
    ({i : P.sharedInstance.Stage // i ≠ stage} → Row)

def overlayFullOtherNoise (P : Parameters) (stage : P.sharedInstance.Stage)
    (seed : OverlayFreshSeed P Seed Row) : OverlayFullOtherNoise P Row stage :=
  ((fun i => seed.2.1 i.val), fun i => seed.2.2 i.val)

noncomputable def overlayFullOtherNoiseLaw (P : Parameters) (rowLaw : Measure Row)
    (stage : P.sharedInstance.Stage) : Measure (OverlayFullOtherNoise P Row stage) :=
  (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => auxiliaryTapeLaw P)).prod
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => rowLaw))

instance overlayFullOtherNoiseLaw_probability (P : Parameters) (rowLaw : Measure Row)
    [IsProbabilityMeasure rowLaw] (stage : P.sharedInstance.Stage) :
    IsProbabilityMeasure (overlayFullOtherNoiseLaw P rowLaw stage) := by
  unfold overlayFullOtherNoiseLaw
  change IsProbabilityMeasure ((Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => auxiliaryTapeLaw P)).prod
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => rowLaw)))
  infer_instance

/-- Both the source's current auxiliary tape and its complete mark row are fresh. -/
theorem overlayFullNoise_other_current (P : Parameters) (rowLaw : Measure Row)
    [IsProbabilityMeasure rowLaw] (stage : P.sharedInstance.Stage) :
    ((simulatorAuxiliaryLaw P).prod (Measure.pi (fun _ : P.sharedInstance.Stage => rowLaw))).map
      (fun noise => (((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => noise.1 i.val),
        fun i : {i : P.sharedInstance.Stage // i ≠ stage} => noise.2 i.val),
        (noise.1 stage, noise.2 stage))) =
      (overlayFullOtherNoiseLaw P rowLaw stage).prod ((auxiliaryTapeLaw P).prod rowLaw) := by
  let splitA := fun values : P.sharedInstance.Stage → P.experiment.Tape =>
    ((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => values i.val), values stage)
  let splitB := fun values : P.sharedInstance.Stage → Row =>
    ((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => values i.val), values stage)
  have ha : Measurable splitA :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val).prodMk (measurable_pi_apply stage)
  have hb : Measurable splitB :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val).prodMk (measurable_pi_apply stage)
  have hA : (simulatorAuxiliaryLaw P).map splitA =
      (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => auxiliaryTapeLaw P)).prod (auxiliaryTapeLaw P) :=
    pi_other_current_jointLaw (auxiliaryTapeLaw P) stage
  have hB : (Measure.pi (fun _ : P.sharedInstance.Stage => rowLaw)).map splitB =
      (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => rowLaw)).prod rowLaw :=
    pi_other_current_jointLaw rowLaw stage
  have hm := Measure.map_prod_map (simulatorAuxiliaryLaw P)
    (Measure.pi (fun _ : P.sharedInstance.Stage => rowLaw)) ha hb
  rw [hA, hB] at hm
  let exchange := fun x : ((({i : P.sharedInstance.Stage // i ≠ stage} → P.experiment.Tape) × P.experiment.Tape) ×
      (({i : P.sharedInstance.Stage // i ≠ stage} → Row) × Row)) => ((x.1.1, x.2.1), (x.1.2, x.2.2))
  have hx : Measurable exchange := by fun_prop
  have h := congrArg (fun ρ => ρ.map exchange) hm.symm
  rw [Measure.map_map hx (ha.prodMap hb)] at h
  exact h.trans (product_exchange_jointLaw
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => auxiliaryTapeLaw P)) (auxiliaryTapeLaw P)
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => rowLaw)) rowLaw)

theorem overlayFullSeed_other_current (P : Parameters) (ν : Measure Seed) (rowLaw : Measure Row)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure rowLaw] (stage : P.sharedInstance.Stage) :
    (overlayFreshSeedLaw P ν rowLaw).map (fun seed =>
      ((seed.1, overlayFullOtherNoise P stage seed), (seed.2.1 stage, seed.2.2 stage))) =
      (ν.prod (overlayFullOtherNoiseLaw P rowLaw stage)).prod ((auxiliaryTapeLaw P).prod rowLaw) := by
  let split := fun noise : (P.sharedInstance.Stage → P.experiment.Tape) × (P.sharedInstance.Stage → Row) =>
    (((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => noise.1 i.val),
      fun i : {i : P.sharedInstance.Stage // i ≠ stage} => noise.2 i.val), (noise.1 stage, noise.2 stage))
  have hs : Measurable split := by fun_prop
  have hm := Measure.map_prod_map ν
    ((simulatorAuxiliaryLaw P).prod (Measure.pi (fun _ : P.sharedInstance.Stage => rowLaw))) measurable_id hs
  rw [Measure.map_id, overlayFullNoise_other_current] at hm
  have h := congrArg (fun ρ => ρ.map MeasurableEquiv.prodAssoc.symm) hm.symm
  rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (measurable_id.prodMap hs)] at h
  exact h.trans (((measurePreserving_prodAssoc ν (overlayFullOtherNoiseLaw P rowLaw stage)
    ((auxiliaryTapeLaw P).prod rowLaw)).symm MeasurableEquiv.prodAssoc).map_eq)

def overlayFullAllOther (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (sample : OverlayFreshSeed P Seed Row × (P.input fee hfee).World) :
    (Seed × OverlayFullOtherNoise P Row stage) × SimulatorOtherWorld P stage :=
  ((sample.1.1, overlayFullOtherNoise P stage sample.1), fun i => sample.2 i.val)

def overlayFullCurrent (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (sample : OverlayFreshSeed P Seed Row × (P.input fee hfee).World) :
    (P.experiment.Tape × Row) × (Bool × P.experiment.Tape) :=
  ((sample.1.2.1 stage, sample.1.2.2 stage), sample.2 stage)

noncomputable def overlayFullAllOtherLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) (rowLaw : Measure Row) (stage : P.sharedInstance.Stage) :
    Measure ((Seed × OverlayFullOtherNoise P Row stage) × SimulatorOtherWorld P stage) :=
  (ν.prod (overlayFullOtherNoiseLaw P rowLaw stage)).prod
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => (P.input fee hfee).stageLaw stage))

theorem overlayFullWorldLaw_allOther_current (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) (rowLaw : Measure Row) [IsProbabilityMeasure ν] [IsProbabilityMeasure rowLaw]
    (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map (fun sample =>
      (overlayFullAllOther P fee hfee stage sample, overlayFullCurrent P fee hfee stage sample)) =
        (overlayFullAllOtherLaw P fee hfee ν rowLaw stage).prod
          (((auxiliaryTapeLaw P).prod rowLaw).prod ((P.input fee hfee).stageLaw stage)) := by
  let splitSeed := fun seed : OverlayFreshSeed P Seed Row =>
    ((seed.1, overlayFullOtherNoise P stage seed), (seed.2.1 stage, seed.2.2 stage))
  let splitWorld := fun world : (P.input fee hfee).World =>
    ((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => world i.val), world stage)
  have hs : Measurable splitSeed := by unfold splitSeed overlayFullOtherNoise; fun_prop
  have hw : Measurable splitWorld :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val).prodMk (measurable_pi_apply stage)
  have hseed := overlayFullSeed_other_current P ν rowLaw stage
  have hworld : (P.input fee hfee).worldLaw.map splitWorld =
      (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => (P.input fee hfee).stageLaw stage)).prod
        ((P.input fee hfee).stageLaw stage) := pi_other_current_jointLaw ((P.input fee hfee).stageLaw stage) stage
  have hm := Measure.map_prod_map (overlayFreshSeedLaw P ν rowLaw) (P.input fee hfee).worldLaw hs hw
  rw [hseed, hworld] at hm
  let exchange := fun x : (((Seed × OverlayFullOtherNoise P Row stage) × (P.experiment.Tape × Row)) ×
      (SimulatorOtherWorld P stage × (Bool × P.experiment.Tape))) => ((x.1.1, x.2.1), (x.1.2, x.2.2))
  have hx : Measurable exchange := by fun_prop
  have h := congrArg (fun ρ => ρ.map exchange) hm.symm
  have hc := Measure.map_map (μ := (overlayFreshSeedLaw P ν rowLaw).prod (P.input fee hfee).worldLaw) hx (hs.prodMap hw)
  exact hc.symm.trans (h.trans (product_exchange_jointLaw (ν.prod (overlayFullOtherNoiseLaw P rowLaw stage))
    ((auxiliaryTapeLaw P).prod rowLaw)
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => (P.input fee hfee).stageLaw stage))
    ((P.input fee hfee).stageLaw stage)))

theorem overlayFullWorldLaw_pastGate {Gate : Type*} [MeasurableSpace Gate]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (ν : Measure Seed) (rowLaw : Measure Row)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure rowLaw] (stage : P.sharedInstance.Stage)
    (gate : ((Seed × OverlayFullOtherNoise P Row stage) × SimulatorOtherWorld P stage) → Gate)
    (hg : Measurable gate) :
    ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map (fun sample =>
      (gate (overlayFullAllOther P fee hfee stage sample), overlayFullCurrent P fee hfee stage sample)) =
        ((overlayFullAllOtherLaw P fee hfee ν rowLaw stage).map gate).prod
          (((auxiliaryTapeLaw P).prod rowLaw).prod ((P.input fee hfee).stageLaw stage)) := by
  have hp : Measurable (Prod.map gate (id : (P.experiment.Tape × Row) × (Bool × P.experiment.Tape) → _)) :=
    hg.prodMap measurable_id
  have hs : Measurable (fun sample : OverlayFreshSeed P Seed Row × (P.input fee hfee).World =>
      (overlayFullAllOther P fee hfee stage sample, overlayFullCurrent P fee hfee stage sample)) := by
    unfold overlayFullAllOther overlayFullCurrent overlayFullOtherNoise
    fun_prop
  have h := congrArg (fun ρ => ρ.map (Prod.map gate id)) (overlayFullWorldLaw_allOther_current P fee hfee ν rowLaw stage)
  have hc := Measure.map_map (μ := (P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)) hp hs
  have hprod := Measure.map_prod_map (overlayFullAllOtherLaw P fee hfee ν rowLaw stage)
    (((auxiliaryTapeLaw P).prod rowLaw).prod ((P.input fee hfee).stageLaw stage)) hg measurable_id
  rw [Measure.map_id] at hprod
  exact hc.symm.trans (h.trans hprod.symm)

end PDROC
