module
public import PaperProofs.Paid.PDROC_LocalRecord_008

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Paid

namespace PDROC
universe u
section
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Exact local source charge on its TRUE first-entry atom. The RHS is the
original stage bill on this entry event, and zero otherwise; later stage
fees are not counted again. All values remain ENNReal. -/
theorem optionalSourceEntryTest_bayesCharge_eq_entryStageBill (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val mode accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (first : P.sharedInstance.Stage) (start : ℕ) :
    P.binarySymmetric.experiment.bayesObservationCharge
      (sourceEntrySeedLaw P fee hfee C mode accounting source ν first start)
      (optionalSourceEntryTest P fee hfee first accounting source.rule source.measurable_rule) =
      ∫⁻ sample, {sample | FirstEntryAt (P.input fee hfee) C.val mode accounting source.rule first.val start sample}.indicator
        (runStageObservationBill (P.input fee hfee) C.val mode accounting source.rule first) sample
          ∂(P.input fee hfee).seededWorldLaw ν := by
  classical
  let input := P.input fee hfee
  let test := optionalSourceEntryTest P fee hfee first accounting source.rule source.measurable_rule
  let f := fun pair : (Seed × Option (Startup P.sharedInstance)) × P.binarySymmetric.experiment.Tape =>
    P.binarySymmetric.experiment.observationCharge (test.rule.stop pair.1 pair.2)
  have hf : Measurable f := (measurable_of_countable P.binarySymmetric.experiment.observationCharge).comp test.measurable_stop
  let joint := fun sample : Seed × input.World =>
    (entrySeedStartupAt input C.val mode accounting source.rule first start sample,
      sourceEntryTape P fee hfee first (input.restrictFreshWorld first.val sample.2))
  have hjoint : Measurable joint :=
    (measurable_entrySeedStartupAt input C.val mode accounting source.rule source.measurable_rule first start).prodMk
      ((measurable_sourceEntryTape P fee hfee first).comp
        ((input.measurable_restrictFreshWorld first.val).comp measurable_snd))
  have hlaw := sourceEntry_joint_auxiliaryTape P fee hfee C mode accounting source ν first start
  rw [bayesObservationCharge_eq_auxiliaryTape_integral]
  change (∫⁻ pair, f pair ∂((input.seededWorldLaw ν).map
      (entrySeedStartupAt input C.val mode accounting source.rule first start)).prod (auxiliaryTapeLaw P)) = _
  rw [← hlaw, lintegral_map hf hjoint]
  apply lintegral_congr
  intro sample
  by_cases he : FirstEntryAt input C.val mode accounting source.rule first.val start sample
  · have hentry : entryStartupAt input C.val mode accounting source.rule first start sample =
        some (publicStartup (run input C.val mode accounting source.rule sample start)) := by
      simp only [entryStartupAt, he, ↓reduceIte]
    change P.binarySymmetric.experiment.observationCharge
      (test.rule.stop (sample.1, entryStartupAt input C.val mode accounting source.rule first start sample) _) = _
    rw [hentry, optionalSourceEntryTest_stop_some,
      sourceEntryTest_observationCharge_eq_stageBill P fee hfee C mode accounting source sample first start he]
    change FirstEntryAt (P.input fee hfee) C.val mode accounting source.rule first.val start sample at he
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left he]
  · have hentry : entryStartupAt input C.val mode accounting source.rule first start sample = none := by
      simp only [entryStartupAt, he, ↓reduceIte]
    change P.binarySymmetric.experiment.observationCharge
      (test.rule.stop (sample.1, entryStartupAt input C.val mode accounting source.rule first start sample) _) = _
    rw [hentry, optionalSourceEntryTest_stop_none, P.binarySymmetric.experiment.observationCharge_zero]
    change ¬ FirstEntryAt (P.input fee hfee) C.val mode accounting source.rule first.val start sample at he
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right he]

end
end PDROC



