module

public import PaperProofs.Paid.PDROC_SimulatorLaw_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v

/-- Generic row noise. A row can contain countably many record-indexed mixture
and false-positive marks; this declaration imposes no independence inside a row. -/
abbrev OverlayFreshSeed (P : Parameters) (Seed : Type u) (Row : Type v) :=
  Seed × ((P.sharedInstance.Stage → P.experiment.Tape) × (P.sharedInstance.Stage → Row))

abbrev OverlayFreshOtherRows (P : Parameters) (Row : Type v) (stage : P.sharedInstance.Stage) :=
  {i : P.sharedInstance.Stage // i ≠ stage} → Row

/-- All auxiliary tapes may be kept in the gate, including the selected current record's tape. -/
abbrev OverlayFreshBase (P : Parameters) (Seed : Type u) (Row : Type v)
    (stage : P.sharedInstance.Stage) :=
  Seed × ((P.sharedInstance.Stage → P.experiment.Tape) × OverlayFreshOtherRows P Row stage)

variable {Seed : Type u} {Row : Type v} [MeasurableSpace Seed] [MeasurableSpace Row]

noncomputable def overlayFreshSeedLaw (P : Parameters) (ν : Measure Seed) (rowLaw : Measure Row) :
    Measure (OverlayFreshSeed P Seed Row) :=
  ν.prod ((simulatorAuxiliaryLaw P).prod (Measure.pi (fun _ : P.sharedInstance.Stage => rowLaw)))

instance overlayFreshSeedLaw_probability (P : Parameters) (ν : Measure Seed) (rowLaw : Measure Row)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure rowLaw] :
    IsProbabilityMeasure (overlayFreshSeedLaw P ν rowLaw) := by
  unfold overlayFreshSeedLaw
  infer_instance

def overlayFreshBase (P : Parameters) (stage : P.sharedInstance.Stage)
    (seed : OverlayFreshSeed P Seed Row) : OverlayFreshBase P Seed Row stage :=
  (seed.1, (seed.2.1, fun i => seed.2.2 i.val))

noncomputable def overlayFreshBaseLaw (P : Parameters) (ν : Measure Seed)
    (rowLaw : Measure Row) (stage : P.sharedInstance.Stage) :
    Measure (OverlayFreshBase P Seed Row stage) :=
  ν.prod ((simulatorAuxiliaryLaw P).prod
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => rowLaw)))

instance overlayFreshBaseLaw_probability (P : Parameters) (ν : Measure Seed) (rowLaw : Measure Row)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure rowLaw] (stage : P.sharedInstance.Stage) :
    IsProbabilityMeasure (overlayFreshBaseLaw P ν rowLaw stage) := by
  unfold overlayFreshBaseLaw
  infer_instance

/-- Exact whole-row freshness with arbitrary original-seed universe. -/
theorem overlayFreshSeedLaw_base_row (P : Parameters) (ν : Measure Seed) (rowLaw : Measure Row)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure rowLaw] (stage : P.sharedInstance.Stage) :
    (overlayFreshSeedLaw P ν rowLaw).map (fun seed =>
      (overlayFreshBase P stage seed, seed.2.2 stage)) =
        (overlayFreshBaseLaw P ν rowLaw stage).prod rowLaw := by
  let otherLaw := Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => rowLaw)
  let splitRow := fun rows : P.sharedInstance.Stage → Row =>
    ((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => rows i.val), rows stage)
  have hm : Measurable splitRow :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val).prodMk (measurable_pi_apply stage)
  have hrow : MeasurePreserving splitRow (Measure.pi (fun _ : P.sharedInstance.Stage => rowLaw))
      (otherLaw.prod rowLaw) :=
    ⟨hm, pi_other_current_jointLaw rowLaw stage⟩
  have h1 := (MeasurePreserving.id ν).prod ((MeasurePreserving.id (simulatorAuxiliaryLaw P)).prod hrow)
  have h2 := (MeasurePreserving.id ν).prod
    ((measurePreserving_prodAssoc (simulatorAuxiliaryLaw P) otherLaw rowLaw).symm MeasurableEquiv.prodAssoc)
  have h3 := (measurePreserving_prodAssoc ν ((simulatorAuxiliaryLaw P).prod otherLaw) rowLaw).symm
    MeasurableEquiv.prodAssoc
  exact ((h3.comp h2).comp h1).map_eq

def overlayFreshAllOther (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (sample : OverlayFreshSeed P Seed Row × (P.input fee hfee).World) :
    OverlayFreshBase P Seed Row stage × SimulatorOtherWorld P stage :=
  (overlayFreshBase P stage sample.1, fun i => sample.2 i.val)

def overlayFreshCurrent (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (sample : OverlayFreshSeed P Seed Row × (P.input fee hfee).World) :
    Row × (Bool × P.experiment.Tape) :=
  (sample.1.2.2 stage, sample.2 stage)

noncomputable def overlayFreshAllOtherLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) (rowLaw : Measure Row) (stage : P.sharedInstance.Stage) :
    Measure (OverlayFreshBase P Seed Row stage × SimulatorOtherWorld P stage) :=
  (overlayFreshBaseLaw P ν rowLaw stage).prod
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => (P.input fee hfee).stageLaw stage))

/-- Current whole row and the real current truth/tape are fresh jointly.
Old seed, full auxiliary tapes, all other rows and all other world coordinates remain. -/
theorem overlayFreshWorldLaw_allOther_current (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) (rowLaw : Measure Row) [IsProbabilityMeasure ν] [IsProbabilityMeasure rowLaw]
    (stage : P.sharedInstance.Stage) :
    ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map (fun sample =>
      (overlayFreshAllOther P fee hfee stage sample, overlayFreshCurrent P fee hfee stage sample)) =
        (overlayFreshAllOtherLaw P fee hfee ν rowLaw stage).prod
          (rowLaw.prod ((P.input fee hfee).stageLaw stage)) := by
  let splitSeed := fun seed : OverlayFreshSeed P Seed Row =>
    (overlayFreshBase P stage seed, seed.2.2 stage)
  let splitWorld := fun world : (P.input fee hfee).World =>
    ((fun i : {i : P.sharedInstance.Stage // i ≠ stage} => world i.val), world stage)
  have hs : Measurable splitSeed := by unfold splitSeed overlayFreshBase; fun_prop
  have hw : Measurable splitWorld :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val).prodMk (measurable_pi_apply stage)
  have hseed := overlayFreshSeedLaw_base_row P ν rowLaw stage
  have hworld : (P.input fee hfee).worldLaw.map splitWorld =
      (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => (P.input fee hfee).stageLaw stage)).prod
        ((P.input fee hfee).stageLaw stage) :=
    pi_other_current_jointLaw ((P.input fee hfee).stageLaw stage) stage
  have hmap := Measure.map_prod_map (overlayFreshSeedLaw P ν rowLaw) (P.input fee hfee).worldLaw hs hw
  rw [hseed, hworld] at hmap
  let exchange := fun x : ((OverlayFreshBase P Seed Row stage × Row) ×
      (SimulatorOtherWorld P stage × (Bool × P.experiment.Tape))) => ((x.1.1, x.2.1), (x.1.2, x.2.2))
  have hx : Measurable exchange := by fun_prop
  have h := congrArg (fun ρ => ρ.map exchange) hmap.symm
  have hc := Measure.map_map (μ := (overlayFreshSeedLaw P ν rowLaw).prod (P.input fee hfee).worldLaw)
    hx (hs.prodMap hw)
  exact hc.symm.trans (h.trans (product_exchange_jointLaw (overlayFreshBaseLaw P ν rowLaw stage) rowLaw
    (Measure.pi (fun _ : {i : P.sharedInstance.Stage // i ≠ stage} => (P.input fee hfee).stageLaw stage))
    ((P.input fee hfee).stageLaw stage)))

/-- Any measurable selected-record/full-virtual-entry gate may be retained,
provided its inputs exclude the current whole row and actual current world. -/
theorem overlayFreshWorldLaw_recordGate {Gate : Type*} [MeasurableSpace Gate]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (ν : Measure Seed) (rowLaw : Measure Row)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure rowLaw] (stage : P.sharedInstance.Stage)
    (gate : (OverlayFreshBase P Seed Row stage × SimulatorOtherWorld P stage) → Gate)
    (hg : Measurable gate) :
    ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map (fun sample =>
      (gate (overlayFreshAllOther P fee hfee stage sample), overlayFreshCurrent P fee hfee stage sample)) =
        ((overlayFreshAllOtherLaw P fee hfee ν rowLaw stage).map gate).prod
          (rowLaw.prod ((P.input fee hfee).stageLaw stage)) := by
  have hp : Measurable (Prod.map gate (id : Row × (Bool × P.experiment.Tape) → _)) :=
    hg.prodMap measurable_id
  have hs : Measurable (fun sample : OverlayFreshSeed P Seed Row × (P.input fee hfee).World =>
      (overlayFreshAllOther P fee hfee stage sample, overlayFreshCurrent P fee hfee stage sample)) := by
    unfold overlayFreshAllOther overlayFreshCurrent overlayFreshBase
    fun_prop
  have h := congrArg (fun ρ => ρ.map (Prod.map gate id))
    (overlayFreshWorldLaw_allOther_current P fee hfee ν rowLaw stage)
  have hc := Measure.map_map (μ := (P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)) hp hs
  have hprod := Measure.map_prod_map (overlayFreshAllOtherLaw P fee hfee ν rowLaw stage)
    (rowLaw.prod ((P.input fee hfee).stageLaw stage)) hg measurable_id
  rw [Measure.map_id] at hprod
  exact hc.symm.trans (h.trans hprod.symm)

end PDROC
