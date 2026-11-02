module

public import PaperProofs.Paid.PDROC_SimulatorLaw_012
public import PaperProofs.Paid.PDROC_TerminalCapture_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Finite local stopping on the ORIGINAL source's actual eventual-stage
sample is derived from its finite full bill, including the no-entry branch. -/
theorem sourceEventualStageSample_finite_ae (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      (simulatorLocalTest P fee hfee (sourceForOptionalHistory source.rule)
        (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage).rule.stop
          (sourceEventualStageSample P fee hfee C accounting source stage sample).1
          (sourceEventualStageSample P fee hfee C accounting source stage sample).2.2 ≠ ⊤ := by
  let input := P.input fee hfee
  let wrapped := sourceForOptionalHistory source.rule
  let hm := measurable_sourceForOptionalHistory source.rule source.measurable_rule
  let test := simulatorLocalTest P fee hfee wrapped hm stage
  let η := sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage
  let stop := fun sample : ((Seed × EntryHistory P.sharedInstance) × List (VisibleEvent P.sharedInstance)) ×
      input.StageSample stage => test.rule.stop sample.1 sample.2.2
  have hstop : Measurable stop := test.measurable_stop.comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hp : MeasurableSet {sample | stop sample ≠ ⊤} := (hstop (measurableSet_singleton ⊤)).compl
  have hf := sourceEventualDraw_finiteET_of_fullBill P fee hfee C accounting source ν stage hfinite
  have hfiniteStage : ∀ᵐ sample ∂η.prod (input.stageLaw stage), stop sample ≠ ⊤ := by
    apply ae_prod_stageLaw_of_conditional input stage η (fun sample => stop sample ≠ ⊤) hp
    intro truth
    exact P.binarySymmetric.experiment.expectedSamples_finite_stop η test truth (hf truth)
  rw [← sourceEventualStageSample_law P fee hfee C accounting source ν stage] at hfiniteStage
  exact (ae_map_iff (measurable_sourceEventualStageSample P fee hfee C accounting source stage).aemeasurable hp).mp hfiniteStage

end PDROC
