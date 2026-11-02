module

public import PaperProofs.Paid.PDROC_FinalCursor_001
public import PaperProofs.Paid.PDROC_Simulator_057
public import PaperProofs.Paid.PDROC_SimulatorLaw_017
public import PaperProofs.Paid.PDROC_TerminalLaw_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The final cursor-N component has the ORIGINAL old-seed × FULL completed
history law. All entry, source/actual tail guards and capture premises are
discharged; only original full-bill finiteness and N>0 remain. N=0 has its
separate complete SourceHistoryLaw theorem. -/
theorem simulator_finalCursorLaw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hpos : 0 < P.sharedInstance.stageCount) :
    (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source.rule)
        (simulatorData P fee hfee source.rule) sample))).restrict
          (completedCursorCell P.sharedInstance Seed P.sharedInstance.stageCount) =
    (((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
      (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample))).restrict
        (completedCursorCell P.sharedInstance Seed P.sharedInstance.stageCount) := by
  let stage : P.sharedInstance.Stage := ⟨P.sharedInstance.stageCount - 1, by
    change P.sharedInstance.stageCount - 1 < P.sharedInstance.stageCount
    omega⟩
  have hlast : stage.val + 1 = P.sharedInstance.stageCount := by
    change P.sharedInstance.stageCount - 1 + 1 = P.sharedInstance.stageCount
    omega
  let μa := (P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)
  let μs := (P.input fee hfee).seededWorldLaw ν
  let completeA := fun sample : SimulatorSeed P Seed × (P.input fee hfee).World =>
    (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source.rule)
      (simulatorData P fee hfee source.rule) sample)
  let completeS := fun sample : Seed × (P.input fee hfee).World =>
    (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample)
  let exitA := simulatorEventualStageExit P fee hfee C accounting source.rule stage
  let exitS := sourceEventualStageExitSome P fee hfee C accounting source stage
  let project := finalCursorTailProjection P.sharedInstance.stageCount source.rule
  have hcA : Measurable completeA := (measurable_fst.comp measurable_fst).prodMk
    (measurable_simulatorShadowCompletedHistory P fee hfee C accounting source.rule source.measurable_rule)
  have hcS : Measurable completeS := measurable_fst.prodMk
    (measurable_completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule source.measurable_rule)
  have heA : Measurable exitA :=
    measurable_simulatorEventualStageExit P fee hfee C accounting source.rule source.measurable_rule stage
  have heS : Measurable exitS := measurable_sourceEventualStageExitSome P fee hfee C accounting source stage
  have hp : Measurable project := measurable_finalCursorTailProjection _ source.rule source.measurable_rule
  have hentry := simulatorVirtualEntryGate_law P fee hfee C accounting source ν hfinite stage
  have hcapA := simulator_finalCursorTail_capture_ae_of_entryLaw P fee hfee C accounting source ν stage hlast hfinite hentry
  have hcapS := source_finalCursorCapture_ae P fee hfee C accounting source ν stage hlast hfinite
  have hA : (μa.map completeA).map (cursorCompletedNatProjection P.sharedInstance.stageCount) =
      (μa.map exitA).map project := by
    rw [Measure.map_map (measurable_cursorCompletedNatProjection _) hcA, Measure.map_map hp heA]
    exact Measure.map_congr hcapA
  have hS : (μs.map completeS).map (cursorCompletedNatProjection P.sharedInstance.stageCount) =
      (μs.map exitS).map project := by
    rw [Measure.map_map (measurable_cursorCompletedNatProjection _) hcS, Measure.map_map hp heS]
    exact Measure.map_congr hcapS
  have hexit : μa.map exitA = μs.map exitS :=
    simulatorEventualStageExit_law P fee hfee C accounting source ν stage hfinite
  apply completedCursor_restrict_eq_of_natProjectionLaw _ _ P.sharedInstance.stageCount
  exact hA.trans ((congrArg (fun ρ => ρ.map project) hexit).trans hS.symm)

end PDROC
