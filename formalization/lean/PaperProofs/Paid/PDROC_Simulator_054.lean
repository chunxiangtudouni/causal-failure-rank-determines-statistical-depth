module

public import PaperProofs.Paid.PDROC_Simulator_053

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The EXACT original complete-history law when there are no stages.
Both genuine policies complete with the original source stop/abandon tail
on the empty history. The old seed is retained, and no finite-bill premise
or semantic source-range assumption is needed. -/
theorem simulatorSourceHistoryLaw_zeroStages
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (hzero : P.sharedInstance.stageCount = 0) :
    P.SourceHistoryLaw fee hfee fee hfee C accounting ν (simulatorSeedLaw P ν)
      source.rule (simulatorPolicy P fee hfee C accounting source).rule
      (simulatorData P fee hfee source.rule) := by
  let input := P.input fee hfee
  let completion := fun seed : Seed => (some (terminalCursorTail source.rule seed []) : EntryHistory P.sharedInstance)
  let tag := fun seed : Seed => (seed, completion seed)
  have htail := (measurable_terminalCursorTail source.rule source.measurable_rule).comp
    (measurable_id.prodMk (measurable_const (a := ([] : List (VisibleEvent P.sharedInstance)))))
  have hcompletion : Measurable completion :=
    (measurable_of_countable (some : List (VisibleEvent P.sharedInstance) → EntryHistory P.sharedInstance)).comp htail
  have htag : Measurable tag := measurable_id.prodMk hcompletion
  have hold : Measurable (fun sample : SimulatorSeed P Seed × input.World => sample.1.1) :=
    measurable_fst.comp measurable_fst
  have hactualCompletion : P.shadowCompletedHistory fee hfee C accounting
      (simulatorPolicy P fee hfee C accounting source).rule (simulatorData P fee hfee source.rule) =
      completion ∘ (fun sample : SimulatorSeed P Seed × input.World => sample.1.1) := by
    funext sample
    exact simulator_shadowCompletedHistory_zeroStages P fee hfee C accounting source hzero sample
  have hactualJoint : (fun sample : SimulatorSeed P Seed × input.World =>
      ((simulatorData P fee hfee source.rule).sourceSeed sample.1,
        P.shadowCompletedHistory fee hfee C accounting (simulatorPolicy P fee hfee C accounting source).rule
          (simulatorData P fee hfee source.rule) sample)) =
      tag ∘ (fun sample : SimulatorSeed P Seed × input.World => sample.1.1) := by
    funext sample
    change (sample.1.1, P.shadowCompletedHistory fee hfee C accounting
      (simulatorPolicy P fee hfee C accounting source).rule (simulatorData P fee hfee source.rule) sample) = _
    rw [simulator_shadowCompletedHistory_zeroStages P fee hfee C accounting source hzero sample]
    rfl
  have hsourceJoint : (fun sample : Seed × input.World =>
      (sample.1, completedHistory input C.val .uncapped accounting source.rule sample)) = tag ∘ Prod.fst := by
    funext sample
    rw [source_completedHistory_zeroStages P fee hfee C accounting source hzero sample]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hactualCompletion]
    exact hcompletion.comp hold
  · change (simulatorSeedLaw P ν).map Prod.fst = ν
    exact simulatorSeedLaw_source P ν
  · rw [hactualJoint, hsourceJoint, ← Measure.map_map htag hold,
      simulatorSeededWorldLaw_sourceSeed P fee hfee ν,
      ← Measure.map_map htag measurable_fst, StatisticalInput.seededWorldLaw_seed]

theorem simulator_completedJointLaw_zeroStages
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (hzero : P.sharedInstance.stageCount = 0) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (simulatorPolicy P fee hfee C accounting source).rule
        (simulatorData P fee hfee source.rule) sample)) =
      ((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
        (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample)) :=
  (simulatorSourceHistoryLaw_zeroStages P fee hfee C accounting source ν hzero).2.2

end PDROC
