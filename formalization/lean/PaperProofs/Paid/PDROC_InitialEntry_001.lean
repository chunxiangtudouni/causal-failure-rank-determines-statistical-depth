module

public import PaperProofs.Paid.PDROC_SimulatorLaw_004
public import PaperProofs.Paid.PDROC_EventualEntry_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem simulatorSeededWorldLaw_sourceSeed (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample => sample.1.1) = ν := by
  calc
    _ = (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map Prod.fst).map Prod.fst :=
      (Measure.map_map measurable_fst measurable_fst).symm
    _ = ν := by rw [StatisticalInput.seededWorldLaw_seed, simulatorSeedLaw_source]

theorem simulatorVirtualEntryGate_stageZero_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage) (hzero : stage.val = 0) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage := by
  let tag := fun seed : Seed => (seed, (some [] : EntryHistory P.sharedInstance))
  have ht : Measurable tag := measurable_id.prodMk measurable_const
  have ha : simulatorVirtualEntryGate P fee hfee C accounting source.rule stage =
      tag ∘ (fun sample : SimulatorSeed P Seed × (P.input fee hfee).World => sample.1.1) := by
    funext sample
    change (sample.1.1, (entryHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source.rule) stage sample).map (simulatorShadow P fee hfee source.rule sample.1)) = _
    rw [entryHistory_stageZero (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source.rule) stage hzero sample]
    rfl
  have hs : entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule stage =
      tag ∘ Prod.fst := by
    funext sample
    change (sample.1, entryHistory (P.input fee hfee) C.val .uncapped accounting source.rule stage sample) = _
    rw [entryHistory_stageZero (P.input fee hfee) C.val .uncapped accounting source.rule stage hzero sample]
    rfl
  have hm : Measurable (fun sample : SimulatorSeed P Seed × (P.input fee hfee).World => sample.1.1) :=
    measurable_fst.comp measurable_fst
  have hmap := Measure.map_map (μ := (P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)) ht hm
  rw [ha, ← hmap, simulatorSeededWorldLaw_sourceSeed]
  unfold sourceEventualEntrySeedLaw
  rw [hs, ← Measure.map_map ht measurable_fst, StatisticalInput.seededWorldLaw_seed]

end PDROC
