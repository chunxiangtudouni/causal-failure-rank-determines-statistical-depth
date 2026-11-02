module

public import PaperProofs.Paid.PDROC_OverlayLaw_004
public import PaperProofs.Paid.PDROC_TerminalSupport_001
public import PaperProofs.Paid.PDROC_TerminalCapture_002
public import PaperProofs.Paid.PDROC_SourceTerminal_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem overlayEventualStageExit_prior (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) :
    (overlayEventualStageExit P fee hfee C accounting source stage sample).1 =
      overlayVirtualEntryGate P fee hfee C accounting source stage sample := by
  rfl

/-- The full exit law transports only the measurable source-tail
permission flag. This does not require a semantic source-world range. -/
theorem overlayEventualStageExit_tailAllowed_ae_of_entryLaw
    [MeasurableSpace Seed]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν),
      terminalExitTailAllowedFlag source.rule
        (overlayEventualStageExit P fee hfee C accounting source.rule stage sample) = true := by
  have hp := (measurable_terminalExitTailAllowedFlag source.rule source.measurable_rule)
    (measurableSet_singleton true)
  have hsource : ∀ᵐ result ∂((P.input 0 (by norm_num)).seededWorldLaw ν).map
      (sourceEventualStageExitSome P 0 (by norm_num) C accounting source stage),
      terminalExitTailAllowedFlag source.rule result = true :=
    (ae_map_iff (measurable_sourceEventualStageExitSome P 0 (by norm_num) C accounting source stage).aemeasurable hp).mpr
      (sourceEventualStageExit_tailAllowed_ae P 0 (by norm_num) C accounting source ν stage hfinite)
  rw [← overlayEventualStageExit_law_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry] at hsource
  exact ae_of_ae_map
    (measurable_overlayEventualStageExit P fee hfee C accounting source.rule source.measurable_rule stage).aemeasurable hsource

/-- Native cursor/halt projections discharge every structural premise
of the generic terminal-capture theorem. The remaining actual-exit
witness is explicitly pathwise, retaining the entire shadow history. -/
theorem overlay_terminalCapture_of_actual_exit (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (hcatch : ∀ entry, entryHistory (P.input fee hfee) C.val .uncapped accounting
        (overlayRule P fee hfee source) stage sample = some entry →
      ∃ clock, (overlayEventualStageExit P fee hfee C accounting source stage sample).2 =
        some (overlayShadow P source sample.1
          (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample clock).history) ∧
        ((run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample clock).halted = true ∨
          stage.val < (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample clock).cursor)) :
    cursorCompletedProjection stage
        (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (overlayRule P fee hfee source)
          (overlayData P source).toRecordSimulatorData sample) =
      terminalExitProjection stage (overlayEventualStageExit P fee hfee C accounting source stage sample) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let view := overlayShadow P source sample.1
  have hl := overlayRule_legal P fee hfee C accounting source
  have hfields (clock : ℕ) :
      historyCursor (view (run input C.val .uncapped accounting actual sample clock).history) =
        (run input C.val .uncapped accounting actual sample clock).cursor ∧
      historyHalted (view (run input C.val .uncapped accounting actual sample clock).history) =
        (run input C.val .uncapped accounting actual sample clock).halted := by
    obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample clock
    have hp := overlayReplay_historyProjection (overlaySeedDraw P source)
      (overlaySeedMark P) (overlaySeedGhost P source) sample.1
      (run input C.val .uncapped accounting actual sample clock).history
    exact ⟨hp.1.symm.trans (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ ap),
      hp.2.2.symm.trans (prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ ap)⟩
  have h := cursorCompletedHistory_eq_terminalExitHistory input C.val .uncapped accounting actual hl sample stage view
    (fun clock => (hfields clock).1) (fun clock => (hfields clock).2)
    (overlayEventualStageExit P fee hfee C accounting source stage sample).2 hcatch
  apply Prod.ext
  · exact (congrArg Prod.fst (overlayEventualStageExit_prior P fee hfee C accounting source stage sample)).symm
  · change cursorCompletedHistory stage
        ((completedHistory input C.val .uncapped accounting actual sample).map view) =
      terminalExitHistory stage (overlayEventualStageExit P fee hfee C accounting source stage sample).1.2
        (overlayEventualStageExit P fee hfee C accounting source stage sample).2
    rw [congrArg Prod.snd (overlayEventualStageExit_prior P fee hfee C accounting source stage sample)]
    exact h

/-- A current entry law and the actual terminal capture determine the
whole old-seed × completed-history restriction at a nonfinal cursor. -/
theorem overlay_completedCursorLaw_of_entryLaw_and_capture
    [MeasurableSpace Seed]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage)
    (hcapture : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν),
      cursorCompletedProjection stage
          (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (overlayRule P fee hfee source.rule)
            (overlayData P source.rule).toRecordSimulatorData sample) =
        terminalExitProjection stage (overlayEventualStageExit P fee hfee C accounting source.rule stage sample)) :
    (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map (fun sample =>
      (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (overlayRule P fee hfee source.rule)
        (overlayData P source.rule).toRecordSimulatorData sample))).restrict
          (completedCursorCell P.sharedInstance Seed stage.val) =
    (((P.input 0 (by norm_num)).seededWorldLaw ν).map (fun sample =>
      (sample.1, completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample))).restrict
        (completedCursorCell P.sharedInstance Seed stage.val) := by
  exact completedCursorLaw_eq_of_stageExitLaw _ _ stage _
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_overlayShadowCompletedHistory P fee hfee C accounting source.rule source.measurable_rule)) _
    (measurable_fst.prodMk (measurable_completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting
      source.rule source.measurable_rule)) _
    (measurable_overlayEventualStageExit P fee hfee C accounting source.rule source.measurable_rule stage) _
    (measurable_sourceEventualStageExitSome P 0 (by norm_num) C accounting source stage)
    (overlayEventualStageExit_law_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry)
    hcapture (sourceEventualStageExit_terminalCapture_ae P 0 (by norm_num) C accounting source ν stage hfinite)

end PDROC
