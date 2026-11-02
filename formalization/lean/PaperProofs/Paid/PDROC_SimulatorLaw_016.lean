module

public import PaperProofs.Paid.PDROC_SimulatorLaw_015
public import PaperProofs.Paid.PDROC_SimulatorFlow_007
public import PaperProofs.Paid.PDROC_SourceTerminal_001
public import PaperProofs.Paid.PDROC_InitialEntry_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem sourceEventualStageExitSome_nextEntry_ae (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage next : P.sharedInstance.Stage)
    (hnext : next.val = stage.val + 1)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule next sample =
        simulatorNextEntryOptionalProjection next (sourceEventualStageExitSome P fee hfee C accounting source stage sample) := by
  filter_upwards [sourceEventualStageSample_finite_ae P fee hfee C accounting source ν stage hfinite] with sample hs
  exact sourceEventualStageExitSome_nextEntry_of_finite P fee hfee C accounting source stage next hnext sample hs

/-- The complete stage kernel supplies the next entry law once its actual
pathwise projection has been identified. This is the measure-composition
step used by finite-stage induction, with no conditional normalization. -/
theorem simulatorVirtualEntryGate_next_law_of_flow (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage next : P.sharedInstance.Stage)
    (hnext : next.val = stage.val + 1)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage)
    (hflow : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν),
      simulatorVirtualEntryGate P fee hfee C accounting source.rule next sample =
        simulatorNextEntryOptionalProjection next
          (simulatorEventualStageExit P fee hfee C accounting source.rule stage sample)) :
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule next) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν next := by
  have hp := measurable_simulatorNextEntryOptionalProjection (Seed := Seed) next
  have hsource := sourceEventualStageExitSome_nextEntry_ae P fee hfee C accounting source ν stage next hnext hfinite
  calc
    _ = ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        (fun sample => simulatorNextEntryOptionalProjection next
          (simulatorEventualStageExit P fee hfee C accounting source.rule stage sample)) := Measure.map_congr hflow
    _ = (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        (simulatorEventualStageExit P fee hfee C accounting source.rule stage)).map
          (simulatorNextEntryOptionalProjection next) :=
      (Measure.map_map hp (measurable_simulatorEventualStageExit P fee hfee C accounting source.rule source.measurable_rule stage)).symm
    _ = (((P.input fee hfee).seededWorldLaw ν).map
        (sourceEventualStageExitSome P fee hfee C accounting source stage)).map
          (simulatorNextEntryOptionalProjection next) := by
      rw [simulatorEventualStageExit_law_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry]
    _ = ((P.input fee hfee).seededWorldLaw ν).map
        (fun sample => simulatorNextEntryOptionalProjection next
          (sourceEventualStageExitSome P fee hfee C accounting source stage sample)) :=
      Measure.map_map hp (measurable_sourceEventualStageExitSome P fee hfee C accounting source stage)
    _ = ((P.input fee hfee).seededWorldLaw ν).map
        (entryHistorySeedRecord (P.input fee hfee) C.val .uncapped accounting source.rule next) :=
      Measure.map_congr (hsource.mono (fun _ h => h.symm))
    _ = _ := rfl

/-- Finite-stage composition, retaining the original private seed and
every eventual full entry history, including all never-entry branches. -/
theorem simulatorVirtualEntryGate_all_law_of_next_flow (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hflow : ∀ stage next : P.sharedInstance.Stage, next.val = stage.val + 1 →
      (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
          sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) →
      ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν),
        simulatorVirtualEntryGate P fee hfee C accounting source.rule next sample =
          simulatorNextEntryOptionalProjection next
            (simulatorEventualStageExit P fee hfee C accounting source.rule stage sample)) :
    ∀ stage : P.sharedInstance.Stage,
      ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
          sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage := by
  have hnat : ∀ n : ℕ, ∀ stage : P.sharedInstance.Stage, stage.val = n →
      ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
        (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
          sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage := by
    intro n
    induction n with
    | zero =>
      intro stage hzero
      exact simulatorVirtualEntryGate_stageZero_law P fee hfee C accounting source ν stage hzero
    | succ n ih =>
      intro next hn
      let stage : P.sharedInstance.Stage := ⟨n, by have h := next.isLt; omega⟩
      have hentry := ih stage rfl
      have hnext : next.val = stage.val + 1 := hn
      exact simulatorVirtualEntryGate_next_law_of_flow P fee hfee C accounting source ν stage next hnext hfinite hentry
        (hflow stage next hnext hentry)
  intro stage
  exact hnat stage.val stage rfl

end PDROC
