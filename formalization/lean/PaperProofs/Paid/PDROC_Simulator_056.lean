module

public import PaperProofs.Paid.PDROC_Simulator_055
public import PaperProofs.Paid.PDROC_SimulatorFlow_010
public import PaperProofs.Paid.PDROC_TerminalSupport_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Actual final-cursor tail capture on the measurable draw/tail guard
events. The complete raw exit RV, original completed shadow, and old seed
are used literally; no virtual-Prefix range or source world is needed. -/
theorem simulator_finalCursorTail_capture_pointwise
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (hlast : stage.val + 1 = P.sharedInstance.stageCount)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (hfinite : ∀ m : ℕ, ∀ coin : Bool, ∃ n : ℕ,
      (P.binarySymmetric.rocEndpointTest m).rule.stop coin
        (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞))
    (hgood : optionalSourceDrawGuardGood (sourceForOptionalHistory source) stage
      (simulatorEventualReportedDraw P fee hfee C accounting source stage sample))
    (htailFlag : terminalExitTailAllowedFlag source
      (simulatorEventualStageExit P fee hfee C accounting source stage sample) = true) :
    cursorCompletedNatProjection P.sharedInstance.stageCount
        (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source)
          (simulatorData P fee hfee source) sample) =
      finalCursorTailProjection P.sharedInstance.stageCount source
        (simulatorEventualStageExit P fee hfee C accounting source stage sample) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let view := simulatorShadow P fee hfee source sample.1
  let exit := (simulatorEventualStageExit P fee hfee C accounting source stage sample).2
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
      ∃ start offset : ℕ, FirstEntryAt input C.val .uncapped accounting actual stage.val start sample ∧
        (∀ k < offset, (run input C.val .uncapped accounting actual sample (start + k)).halted = false ∧
          (run input C.val .uncapped accounting actual sample (start + k)).cursor = stage.val) ∧
        exit = some (view (run input C.val .uncapped accounting actual sample (start + offset)).history) ∧
        ((run input C.val .uncapped accounting actual sample (start + offset)).halted = true ∨
          (run input C.val .uncapped accounting actual sample (start + offset)).cursor = stage.val + 1) := by
    intro entry he
    obtain ⟨draw, hd, hg⟩ := simulator_entry_drawGood_of_eventualReportedDraw P fee hfee C accounting source stage sample hgood entry he
    exact simulatorEventualStageExit_minimal_catch_of_guardGood P fee hfee C accounting source stage sample entry he draw hd
      (hfinite draw.record.level (sample.1.2.2 stage)) hg
  have htail : ∀ entry clock, entryHistory input C.val .uncapped accounting actual stage sample = some entry →
      exit = some (view (run input C.val .uncapped accounting actual sample clock).history) →
      (run input C.val .uncapped accounting actual sample clock).halted = false →
      (run input C.val .uncapped accounting actual sample clock).cursor = P.sharedInstance.stageCount →
      (completedHistory input C.val .uncapped accounting actual sample).map view =
        some (terminalCursorTail source sample.1.1 (view (run input C.val .uncapped accounting actual sample clock).history)) := by
    intro entry clock he hx ha hc
    have hprior : (simulatorEventualStageExit P fee hfee C accounting source stage sample).1.2.isSome = true := by
      rw [simulatorEventualStageExit_prior]
      change ((entryHistory input C.val .uncapped accounting actual stage sample).map view).isSome = true
      rw [he]
      rfl
    have hpermit := terminalExitTailAllowedFlag_permission source
      (simulatorEventualStageExit P fee hfee C accounting source stage sample)
      (view (run input C.val .uncapped accounting actual sample clock).history) hx hprior
      ((hfields clock).1.trans hc) ((hfields clock).2.trans ha) htailFlag
    change historyAllowsAction (view (run input C.val .uncapped accounting actual sample clock).history)
      (source sample.1.1 (view (run input C.val .uncapped accounting actual sample clock).history)) at hpermit
    exact simulator_terminalCursor_shadowCompletedHistory P fee hfee C accounting source sample clock hc (fun _ => hpermit)
  have h := finalCursorHistory_eq_tailProjection_of_minimal_exit input C.val .uncapped accounting actual hl sample stage hlast view
    (fun clock => (hfields clock).1) (fun clock => (hfields clock).2) source sample.1.1 exit hcatch htail
  have hrv : simulatorEventualStageExit P fee hfee C accounting source stage sample =
      ((sample.1.1, (entryHistory input C.val .uncapped accounting actual stage sample).map view), exit) := by
    apply Prod.ext
    · exact simulatorEventualStageExit_prior P fee hfee C accounting source stage sample
    · rfl
  rw [hrv]
  exact h

end PDROC
