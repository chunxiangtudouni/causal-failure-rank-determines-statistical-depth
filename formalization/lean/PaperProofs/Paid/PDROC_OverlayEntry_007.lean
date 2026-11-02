module

public import PaperProofs.Paid.PDROC_OverlayEntry_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Identify the representative factor's marginal with the actual generated
old-seed/full-entry law; no source-entry equality is assumed. -/
theorem overlayVirtualEntryFactor_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (rowLaw : Measure OverlayStageCoins) [IsProbabilityMeasure rowLaw]
    (stage : P.sharedInstance.Stage) (row : OverlayStageCoins) :
    (overlayFullAllOtherLaw P fee hfee ν rowLaw stage).map
        (overlayVirtualEntryFactor P fee hfee C accounting source stage row) =
      ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map
        (overlayVirtualEntryGate P fee hfee C accounting source stage) := by
  have hg : Measurable (overlayVirtualEntryGate P fee hfee C accounting source stage) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_overlayVirtualEntry P fee hfee C accounting source hm stage)
  have hn : Measurable (overlayFullCurrent (Seed := Seed) (Row := OverlayStageCoins) P fee hfee stage) := by
    unfold overlayFullCurrent
    fun_prop
  have h := congrArg (fun μ => μ.map Prod.fst)
    (overlayVirtualEntry_joint_freshStage P fee hfee C accounting source hm ν rowLaw stage row)
  have hc := Measure.map_map
    (μ := (P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)) measurable_fst (hg.prodMk hn)
  have hmAux : ((auxiliaryTapeLaw P).prod rowLaw) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ, measure_univ, mul_one]
  have hmNoise : (((auxiliaryTapeLaw P).prod rowLaw).prod ((P.input fee hfee).stageLaw stage)) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, hmAux, measure_univ, mul_one]
  have hfNoise : SFinite ((((auxiliaryTapeLaw P).prod rowLaw).prod ((P.input fee hfee).stageLaw stage)) :
      Measure ((P.experiment.Tape × OverlayStageCoins) × (Bool × P.experiment.Tape))) := by
    change SFinite ((((auxiliaryTapeLaw P).prod rowLaw).prod ((P.input fee hfee).stageLaw stage)) :
      Measure ((P.binarySymmetric.experiment.Tape × OverlayStageCoins) × (P.input fee hfee).StageSample stage))
    infer_instance
  have hf : (((overlayFullAllOtherLaw P fee hfee ν rowLaw stage).map
      (overlayVirtualEntryFactor P fee hfee C accounting source stage row)).prod
        (((auxiliaryTapeLaw P).prod rowLaw).prod ((P.input fee hfee).stageLaw stage))).map
        (Prod.fst : (Seed × EntryHistory P.sharedInstance) ×
          ((P.experiment.Tape × OverlayStageCoins) × (Bool × P.experiment.Tape)) → _) =
      ((((auxiliaryTapeLaw P).prod rowLaw).prod ((P.input fee hfee).stageLaw stage)) Set.univ) •
        ((overlayFullAllOtherLaw P fee hfee ν rowLaw stage).map
          (overlayVirtualEntryFactor P fee hfee C accounting source stage row)) :=
    @Measure.map_fst_prod _ _ _ _ _ _ hfNoise
  exact (hc.symm.trans (h.trans (hf.trans (by rw [hmNoise, one_smul])))).symm

/-- The form consumed by stage-law induction: the first factor is the REAL
current entry marginal, ready for replacement by a proved source-entry law. -/
theorem overlayVirtualEntry_joint_actualMarginal (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (rowLaw : Measure OverlayStageCoins) [IsProbabilityMeasure rowLaw]
    (stage : P.sharedInstance.Stage) (row : OverlayStageCoins) :
    ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map (fun sample =>
      (overlayVirtualEntryGate P fee hfee C accounting source stage sample, overlayFullCurrent P fee hfee stage sample)) =
      (((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map
        (overlayVirtualEntryGate P fee hfee C accounting source stage)).prod
          (((auxiliaryTapeLaw P).prod rowLaw).prod ((P.input fee hfee).stageLaw stage)) := by
  have h := overlayVirtualEntry_joint_freshStage P fee hfee C accounting source hm ν rowLaw stage row
  rwa [overlayVirtualEntryFactor_law P fee hfee C accounting source hm ν rowLaw stage row] at h

theorem overlayRecordGateFactor_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (rowLaw : Measure OverlayStageCoins) [IsProbabilityMeasure rowLaw]
    (stage : P.sharedInstance.Stage) (row : OverlayStageCoins) :
    (overlayFreshAllOtherLaw P fee hfee ν rowLaw stage).map
        (overlayFreshGateFactor P fee hfee stage row (false, simulatorDummyTape P)
          (overlayRecordGate P fee hfee C accounting source stage)) =
      ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map
        (overlayRecordGate P fee hfee C accounting source stage) := by
  have hg := measurable_overlayRecordGate P fee hfee C accounting source hm stage
  have hn : Measurable (overlayFreshCurrent (Seed := Seed) (Row := OverlayStageCoins) P fee hfee stage) := by
    unfold overlayFreshCurrent
    fun_prop
  have h := congrArg (fun μ => μ.map Prod.fst)
    (overlayRecordGate_joint_freshEndpoint P fee hfee C accounting source hm ν rowLaw stage row)
  have hc := Measure.map_map
    (μ := (P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)) measurable_fst (hg.prodMk hn)
  have hmNoise : (rowLaw.prod ((P.input fee hfee).stageLaw stage)) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ, measure_univ, mul_one]
  have hfNoise : SFinite ((rowLaw.prod ((P.input fee hfee).stageLaw stage)) :
      Measure (OverlayStageCoins × (Bool × P.experiment.Tape))) := by
    change SFinite ((rowLaw.prod ((P.input fee hfee).stageLaw stage)) :
      Measure (OverlayStageCoins × (P.input fee hfee).StageSample stage))
    infer_instance
  have hf : (((overlayFreshAllOtherLaw P fee hfee ν rowLaw stage).map
      (overlayFreshGateFactor P fee hfee stage row (false, simulatorDummyTape P)
        (overlayRecordGate P fee hfee C accounting source stage))).prod
        (rowLaw.prod ((P.input fee hfee).stageLaw stage))).map Prod.fst =
      ((rowLaw.prod ((P.input fee hfee).stageLaw stage)) Set.univ) •
        ((overlayFreshAllOtherLaw P fee hfee ν rowLaw stage).map
          (overlayFreshGateFactor P fee hfee stage row (false, simulatorDummyTape P)
            (overlayRecordGate P fee hfee C accounting source stage))) :=
    @Measure.map_fst_prod _ _ _ _ _ _ hfNoise
  exact (hc.symm.trans (h.trans (hf.trans (by rw [hmNoise, one_smul])))).symm

theorem overlayRecordGate_joint_actualMarginal (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (rowLaw : Measure OverlayStageCoins) [IsProbabilityMeasure rowLaw]
    (stage : P.sharedInstance.Stage) (row : OverlayStageCoins) :
    ((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map (fun sample =>
      (overlayRecordGate P fee hfee C accounting source stage sample, overlayFreshCurrent P fee hfee stage sample)) =
      (((P.input fee hfee).seededWorldLaw (overlayFreshSeedLaw P ν rowLaw)).map
        (overlayRecordGate P fee hfee C accounting source stage)).prod
          (rowLaw.prod ((P.input fee hfee).stageLaw stage)) := by
  have h := overlayRecordGate_joint_freshEndpoint P fee hfee C accounting source hm ν rowLaw stage row
  rwa [overlayRecordGateFactor_law P fee hfee C accounting source hm ν rowLaw stage row] at h

end PDROC
