module

public import PaperProofs.Paid.PDROC_SimulatorLaw_016
public import PaperProofs.Paid.PDROC_SimulatorFlow_008
public import PaperProofs.Paid.PDROC_EndpointFinite_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem simulatorEventualStageExit_nextEntry_ae_of_entryLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage next : P.sharedInstance.Stage)
    (hnext : next.val = stage.val + 1)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν),
      simulatorVirtualEntryGate P fee hfee C accounting source.rule next sample =
        simulatorNextEntryOptionalProjection next
          (simulatorEventualStageExit P fee hfee C accounting source.rule stage sample) := by
  filter_upwards [simulatorEventualReportedDraw_guardGood_ae_of_entryLaw P fee hfee C accounting
    source ν stage hfinite hentry, allEndpoints_finite_seededWorld P fee hfee (simulatorSeedLaw P ν)] with sample hg hf
  exact simulatorEventualStageExit_nextEntry_of_guardGood P fee hfee C accounting source.rule stage next hnext
    sample hg (hf stage)

/-- The concrete simulator preserves the complete original source seed and
every eventual full entry history. All intermediate entry and guard premises
are discharged by finite-stage induction on the actual generated process. -/
theorem simulatorVirtualEntryGate_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ stage : P.sharedInstance.Stage,
      ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
          sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage := by
  apply simulatorVirtualEntryGate_all_law_of_next_flow P fee hfee C accounting source ν hfinite
  intro stage next hnext hentry
  exact simulatorEventualStageExit_nextEntry_ae_of_entryLaw P fee hfee C accounting source ν
    stage next hnext hfinite hentry

/-- Every complete full-stage exit law is consequently exact, without an
entry-law or policy-performance assumption. -/
theorem simulatorEventualStageExit_law (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorEventualStageExit P fee hfee C accounting source.rule stage) =
      ((P.input fee hfee).seededWorldLaw ν).map (sourceEventualStageExitSome P fee hfee C accounting source stage) :=
  simulatorEventualStageExit_law_of_entryLaw P fee hfee C accounting source ν stage hfinite
    (simulatorVirtualEntryGate_law P fee hfee C accounting source ν hfinite stage)

theorem simulatorEventualReportedDraw_guardGood_ae (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν),
      optionalSourceDrawGuardGood (sourceForOptionalHistory source.rule) stage
        (simulatorEventualReportedDraw P fee hfee C accounting source.rule stage sample) :=
  simulatorEventualReportedDraw_guardGood_ae_of_entryLaw P fee hfee C accounting source ν stage hfinite
    (simulatorVirtualEntryGate_law P fee hfee C accounting source ν hfinite stage)

end PDROC
