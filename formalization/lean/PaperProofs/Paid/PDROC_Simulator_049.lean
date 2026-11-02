module

public import PaperProofs.Paid.PDROC_Simulator_048

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Concrete actual terminal capture for the exact eventual-exit RV, under
the finite endpoint event and the visible draw-guard event. Its eventual
almost-sure specialization transports only measurable source guard sets. -/
theorem simulator_cursorCompleted_eq_terminalExit_pointwise
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (hfinite : ∀ m : ℕ, ∀ coin : Bool, ∃ n : ℕ,
      (P.binarySymmetric.rocEndpointTest m).rule.stop coin
        (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞))
    (hgood : ∀ entry, entryHistory (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source) stage sample = some entry →
      ∃ draw : SimulatorDraw P.sharedInstance,
        simulatorSeedDraw P fee hfee source sample.1 stage
          (simulatorShadow P fee hfee source sample.1 entry) = some draw ∧
        sourceDrawGuardGood source stage
          (((sample.1.1, simulatorShadow P fee hfee source sample.1 entry), draw),
            recordVirtualTruth P draw.record ((P.input fee hfee).truthAt sample.2 stage)
              (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage))) :
    cursorCompletedHistory stage
        (P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source)
          (simulatorData P fee hfee source) sample) =
      terminalExitHistory stage (simulatorVirtualEntry P fee hfee C accounting source stage sample)
        (simulatorEventualStageExit P fee hfee C accounting source stage sample).2 := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let view := simulatorShadow P fee hfee source sample.1
  have hl := simulatorRule_legal P fee hfee C accounting source
  have hfields (clock : ℕ) :
      historyCursor (view (run input C.val .uncapped accounting actual sample clock).history) =
        (run input C.val .uncapped accounting actual sample clock).cursor ∧
      historyHalted (view (run input C.val .uncapped accounting actual sample clock).history) =
        (run input C.val .uncapped accounting actual sample clock).halted := by
    obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample clock
    have hp := simulatorReplay_sameProjection (simulatorSeedDraw P fee hfee source) sample.1
      (run input C.val .uncapped accounting actual sample clock).history
    exact ⟨hp.1.symm.trans (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ ap),
      hp.2.2.2.2.symm.trans (prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ ap)⟩
  have hcatch : ∀ entry, entryHistory input C.val .uncapped accounting actual stage sample = some entry →
      ∃ clock, (simulatorEventualStageExit P fee hfee C accounting source stage sample).2 =
          some (view (run input C.val .uncapped accounting actual sample clock).history) ∧
        ((run input C.val .uncapped accounting actual sample clock).halted = true ∨
          stage.val < (run input C.val .uncapped accounting actual sample clock).cursor) := by
    intro entry he
    obtain ⟨draw, hd, hg⟩ := hgood entry he
    exact simulatorEventualStageExit_catch_of_guardGood P fee hfee C accounting source stage sample entry he draw hd
      (hfinite draw.record.level (sample.1.2.2 stage)) hg
  exact cursorCompletedHistory_eq_terminalExitHistory input C.val .uncapped accounting actual hl sample stage view
    (fun clock => (hfields clock).1) (fun clock => (hfields clock).2)
    (simulatorEventualStageExit P fee hfee C accounting source stage sample).2 hcatch

end PDROC
