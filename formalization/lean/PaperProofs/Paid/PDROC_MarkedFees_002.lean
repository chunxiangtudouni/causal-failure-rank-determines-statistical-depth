module

public import PaperProofs.Paid.PDROC_MarkedFees_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v

local instance {I : Instance} : MeasurableSpace (Option (List (HistoryMark I))) := ⊤
local instance {I : Instance} : MeasurableSingletonClass (Option (List (HistoryMark I))) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

theorem actualCorrectionBillLaw_eq_markedCompletedLaw (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type u} [MeasurableSpace Seed]
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed) (ν : Measure Seed)
    (hnone : (P.input fee hfee).seededWorldLaw ν {sample |
      completedHistory (P.input fee hfee) C.val mode accounting policy.rule sample = none} = 0) :
    P.actualCorrectionBillLaw fee hfee C mode accounting policy.rule ν =
      (((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
        (completedHistory (P.input fee hfee) C.val mode accounting policy.rule sample).map markedHistory)).map
          (markedCompletedCorrectionBill fee) := by
  have hm : Measurable (fun sample : Seed × (P.input fee hfee).World =>
      (completedHistory (P.input fee hfee) C.val mode accounting policy.rule sample).map markedHistory) :=
    (measurable_of_countable (fun history : EntryHistory P.sharedInstance => history.map markedHistory)).comp
      (measurable_completedHistory (P.input fee hfee) C.val mode accounting policy.rule policy.measurable_rule)
  have hd : Measurable (markedCompletedCorrectionBill (I := P.sharedInstance) fee) := measurable_of_countable _
  rw [Measure.map_map hd hm]
  unfold PaperProofs.Paid.Parameters.actualCorrectionBillLaw
  apply Measure.map_congr
  have hae : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      completedHistory (P.input fee hfee) C.val mode accounting policy.rule sample ≠ none := by
    apply ae_iff.mpr
    simpa only [not_not] using hnone
  filter_upwards [hae] with sample hs
  cases hh : completedHistory (P.input fee hfee) C.val mode accounting policy.rule sample with
  | none => exact (hs hh).elim
  | some history =>
    simpa only [Function.comp_apply, hh, Option.map_some] using
      paid_runCorrectionBill_of_completedHistory P fee hfee C mode accounting policy.rule policy.legal sample history hh

/-- D06's all-failure actual correction-fee law follows from the ORIGINAL
joint virtual-history law and the pathwise marked-history coupling. No
success conditioning, mean-only substitution, or finite penalty is used. -/
theorem actualCorrectionBillLaw_eq_of_sourceHistoryLaw (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {SourceSeed : Type u} {SimSeed : Type v} [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (hm : RecordSimulatorMeasurable data)
    (hlaw : P.SourceHistoryLaw fee hfee fee hfee C accounting νsource νactual source.rule actual.rule data)
    (hnoneSource : (P.input fee hfee).seededWorldLaw νsource {sample |
      completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample = none} = 0)
    (hnoneActual : (P.input fee hfee).seededWorldLaw νactual {sample |
      completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample = none} = 0)
    (hmarks : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw νactual,
      (completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample).map markedHistory =
        (P.shadowCompletedHistory fee hfee C accounting actual.rule data sample).map markedHistory) :
    P.actualCorrectionBillLaw fee hfee C .uncapped accounting actual.rule νactual =
      P.actualCorrectionBillLaw fee hfee C .uncapped accounting source.rule νsource := by
  have hma : Measurable (fun sample : SimSeed × (P.input fee hfee).World =>
      (data.sourceSeed sample.1, P.shadowCompletedHistory fee hfee C accounting actual.rule data sample)) :=
    (hm.1.comp measurable_fst).prodMk hlaw.1
  have hms : Measurable (fun sample : SourceSeed × (P.input fee hfee).World =>
      (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample)) :=
    measurable_fst.prodMk (measurable_completedHistory (P.input fee hfee) C.val .uncapped accounting
      source.rule source.measurable_rule)
  let project := fun pair : SourceSeed × EntryHistory P.sharedInstance => pair.2.map markedHistory
  have hmp : Measurable project := (measurable_of_countable
    (fun history : EntryHistory P.sharedInstance => history.map markedHistory)).comp measurable_snd
  have h := congrArg (fun μ => μ.map project) hlaw.2.2
  rw [Measure.map_map hmp hma, Measure.map_map hmp hms] at h
  have hmarkedLaw : ((P.input fee hfee).seededWorldLaw νactual).map (fun sample =>
      (completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample).map markedHistory) =
    ((P.input fee hfee).seededWorldLaw νsource).map (fun sample =>
      (completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample).map markedHistory) :=
    (Measure.map_congr hmarks).trans h
  rw [actualCorrectionBillLaw_eq_markedCompletedLaw P fee hfee C .uncapped accounting actual νactual hnoneActual,
    actualCorrectionBillLaw_eq_markedCompletedLaw P fee hfee C .uncapped accounting source νsource hnoneSource,
    hmarkedLaw]

end PDROC
