module

public import PaperProofs.Paid.PDROC_SimulatorLaw_018
public import PaperProofs.Paid.PDROC_Simulator_054
public import PaperProofs.Paid.PDROC_FinalCursor_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- All ordinary cursor components have already been derived from the
actual stage kernels. The final cursor component completes the ORIGINAL
joint source-seed/full-history law. -/
theorem simulatorSourceHistoryLaw_of_lastCursorLaw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hlast : (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source.rule)
        (simulatorData P fee hfee source.rule) sample))).restrict
          (completedCursorCell P.sharedInstance Seed P.sharedInstance.stageCount) =
      (((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
        (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample))).restrict
          (completedCursorCell P.sharedInstance Seed P.sharedInstance.stageCount)) :
    P.SourceHistoryLaw fee hfee fee hfee C accounting ν (simulatorSeedLaw P ν)
      source.rule (simulatorPolicy P fee hfee C accounting source).rule (simulatorData P fee hfee source.rule) := by
  apply simulatorSourceHistoryLaw_of_cursor_restrictions P fee hfee C accounting source ν hfinite
  intro cursor
  by_cases hc : cursor.val < P.sharedInstance.stageCount
  · exact simulator_completedCursorLaw P fee hfee C accounting source ν ⟨cursor.val, hc⟩ hfinite
  · have heq : cursor.val = P.sharedInstance.stageCount := by have hbound := cursor.isLt; omega
    rw [heq]
    exact hlast

/-- The ORIGINAL full private-source-seed × completed-shadow-history law
for the concrete simulator. The proof composes its generated stage kernels,
retains all failed and abandoned histories, and handles zero stages. -/
theorem simulatorSourceHistoryLaw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    P.SourceHistoryLaw fee hfee fee hfee C accounting ν (simulatorSeedLaw P ν)
      source.rule (simulatorPolicy P fee hfee C accounting source).rule (simulatorData P fee hfee source.rule) := by
  by_cases hzero : P.sharedInstance.stageCount = 0
  · exact simulatorSourceHistoryLaw_zeroStages P fee hfee C accounting source ν hzero
  · apply simulatorSourceHistoryLaw_of_lastCursorLaw P fee hfee C accounting source ν hfinite
    exact simulator_finalCursorLaw P fee hfee C accounting source ν hfinite (by omega)

end PDROC
