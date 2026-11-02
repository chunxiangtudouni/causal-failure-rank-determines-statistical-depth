module

public import PaperProofs.Paid.PDROC_SimulatorFlow_007
public import PaperProofs.Paid.PDROC_Simulator_051

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Whole actual-sample next-entry flow from the measurable optional Good
predicate and finite current endpoint tests. Missing prior entry is preserved. -/
theorem simulatorEventualStageExit_nextEntry_of_guardGood (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage next : P.sharedInstance.Stage)
    (hnext : next.val = stage.val + 1)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (hgood : optionalSourceDrawGuardGood (sourceForOptionalHistory source) stage
      (simulatorEventualReportedDraw P fee hfee C accounting source stage sample))
    (hfinite : ∀ (m : ℕ) (coin : Bool), ∃ n : ℕ,
      (P.binarySymmetric.rocEndpointTest m).rule.stop coin (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞)) :
    simulatorVirtualEntryGate P fee hfee C accounting source next sample =
      simulatorNextEntryOptionalProjection next (simulatorEventualStageExit P fee hfee C accounting source stage sample) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  cases he : entryHistory input C.val .uncapped accounting actual stage sample with
  | none =>
    have hn := entryHistory_next_none_of_prior_none input C.val .uncapped accounting actual
      (simulatorRule_legal P fee hfee C accounting source) sample stage next (by omega) he
    have hleft : simulatorVirtualEntryGate P fee hfee C accounting source next sample = (sample.1.1, none) := by
      change (sample.1.1, (entryHistory input C.val .uncapped accounting actual next sample).map _) = _
      rw [hn, Option.map_none]
    have hprior : (simulatorEventualStageExit P fee hfee C accounting source stage sample).1 = (sample.1.1, none) := by
      rw [simulatorEventualStageExit_prior]
      change (sample.1.1, (entryHistory input C.val .uncapped accounting actual stage sample).map _) = _
      rw [he, Option.map_none]
    rw [hleft]
    symm
    change simulatorNextEntryOptionalProjection next
      ((simulatorEventualStageExit P fee hfee C accounting source stage sample).1,
        (simulatorEventualStageExit P fee hfee C accounting source stage sample).2) = _
    rw [hprior]
    exact simulatorNextEntryOptionalProjection_no_prior next _ _
  | some entry =>
    obtain ⟨draw, hd, hg⟩ := simulator_entry_drawGood_of_eventualReportedDraw P fee hfee C accounting source stage sample hgood entry he
    obtain ⟨start, hc, hbefore, hhistory⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage sample entry).mp he
    have hdraw : simulatorSeedDraw P fee hfee source sample.1 stage
        (simulatorShadow P fee hfee source sample.1 (run input C.val .uncapped accounting actual sample start).history) = some draw := by
      rw [hhistory]
      exact hd
    have hguard : sourceDrawGuardGood source stage
        (((sample.1.1, simulatorShadow P fee hfee source sample.1
          (run input C.val .uncapped accounting actual sample start).history), draw),
            recordVirtualTruth P draw.record (input.truthAt sample.2 stage)
              (sample.1.2.2 stage, worldTapes input sample.2 stage)) := by
      rw [hhistory]
      exact hg
    have hflow := simulator_nextEntry_projection_of_guardGood P fee hfee C accounting source sample.1 sample.2
      start stage next hnext ⟨hc, hbefore⟩ draw hdraw (hfinite draw.record.level (sample.1.2.2 stage)) hguard
    rw [hhistory] at hflow
    rw [simulatorEventualStageExit_of_entry_draw P fee hfee C accounting source stage sample entry he draw hd,
      simulatorNextEntryOptionalProjection_some]
    rw [sourceDrawStageExit_optionalHistory_some] at hflow
    exact hflow

end PDROC
