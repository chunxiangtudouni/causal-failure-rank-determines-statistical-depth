module

public import PaperProofs.Paid.PDROC_OverlayLaw_006
public import PaperProofs.Paid.PDROC_FinalCursor_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- The actual first stage exit, retaining both its genuine first-entry
clock and every preceding active native state. -/
def OverlayMinimalExitCaptured (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World) : Prop :=
  ∀ entry, entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) stage sample = some entry →
    ∃ start offset : ℕ,
      FirstEntryAt (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
        stage.val start sample ∧
      (∀ k < offset,
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + k)).halted = false ∧
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + k)).cursor = stage.val) ∧
      (overlayEventualStageExit P fee hfee C accounting source stage sample).2 =
        some (overlayShadow P source sample.1
          (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + offset)).history) ∧
      ((run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + offset)).halted = true ∨
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + offset)).cursor = stage.val + 1)

theorem overlay_terminalCapture_of_minimal_exit (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (hcapture : OverlayMinimalExitCaptured P fee hfee C accounting source stage sample) :
    cursorCompletedProjection stage
        (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (overlayRule P fee hfee source)
          (overlayData P source).toRecordSimulatorData sample) =
      terminalExitProjection stage (overlayEventualStageExit P fee hfee C accounting source stage sample) := by
  apply overlay_terminalCapture_of_actual_exit P fee hfee C accounting source stage sample
  intro entry he
  obtain ⟨start, offset, _hfirst, _hbefore, hx, hexit⟩ := hcapture entry he
  refine ⟨start + offset, hx, hexit.imp id ?_⟩
  intro hc
  omega

/-- The exact actual cursor-N completion is the shared source tail
projection of its genuine minimal last-stage exit. Ghost work vanishes
at N; the source-tail permission is the explicit visible flag. -/
theorem overlay_finalCursorTail_capture_of_minimal_exit
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (hlast : stage.val + 1 = P.sharedInstance.stageCount)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (hcapture : OverlayMinimalExitCaptured P fee hfee C accounting source stage sample)
    (htailFlag : terminalExitTailAllowedFlag source
      (overlayEventualStageExit P fee hfee C accounting source stage sample) = true) :
    cursorCompletedNatProjection P.sharedInstance.stageCount
        (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (overlayRule P fee hfee source)
          (overlayData P source).toRecordSimulatorData sample) =
      finalCursorTailProjection P.sharedInstance.stageCount source
        (overlayEventualStageExit P fee hfee C accounting source stage sample) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let view := overlayShadow P source sample.1
  let exit := (overlayEventualStageExit P fee hfee C accounting source stage sample).2
  have hl := overlayRule_legal P fee hfee C accounting source
  have hfields (clock : ℕ) :
      historyCursor (view (run input C.val .uncapped accounting actual sample clock).history) =
        (run input C.val .uncapped accounting actual sample clock).cursor ∧
      historyHalted (view (run input C.val .uncapped accounting actual sample clock).history) =
        (run input C.val .uncapped accounting actual sample clock).halted := by
    obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample clock
    have hp := overlayReplay_historyProjection (overlaySeedDraw P source) (overlaySeedMark P)
      (overlaySeedGhost P source) sample.1 (run input C.val .uncapped accounting actual sample clock).history
    exact ⟨hp.1.symm.trans (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ ap),
      hp.2.2.symm.trans (prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ ap)⟩
  have htail : ∀ entry clock, entryHistory input C.val .uncapped accounting actual stage sample = some entry →
      exit = some (view (run input C.val .uncapped accounting actual sample clock).history) →
      (run input C.val .uncapped accounting actual sample clock).halted = false →
      (run input C.val .uncapped accounting actual sample clock).cursor = P.sharedInstance.stageCount →
      (completedHistory input C.val .uncapped accounting actual sample).map view =
        some (terminalCursorTail source sample.1.1 (view (run input C.val .uncapped accounting actual sample clock).history)) := by
    intro entry clock he hx ha hc
    have hprior : (overlayEventualStageExit P fee hfee C accounting source stage sample).1.2.isSome = true := by
      rw [overlayEventualStageExit_prior]
      change ((entryHistory input C.val .uncapped accounting actual stage sample).map view).isSome = true
      rw [he]
      rfl
    have hpermit := terminalExitTailAllowedFlag_permission source
      (overlayEventualStageExit P fee hfee C accounting source stage sample)
      (view (run input C.val .uncapped accounting actual sample clock).history) hx hprior
      ((hfields clock).1.trans hc) ((hfields clock).2.trans ha) htailFlag
    change historyAllowsAction (view (run input C.val .uncapped accounting actual sample clock).history)
      (source sample.1.1 (view (run input C.val .uncapped accounting actual sample clock).history)) at hpermit
    exact overlay_terminalCursor_shadowCompletedHistory P fee hfee C accounting source sample clock hc (fun _ => hpermit)
  have h := finalCursorHistory_eq_tailProjection_of_minimal_exit input C.val .uncapped accounting actual hl sample stage hlast view
    (fun clock => (hfields clock).1) (fun clock => (hfields clock).2) source sample.1.1 exit hcapture htail
  have hrv : overlayEventualStageExit P fee hfee C accounting source stage sample =
      ((sample.1.1, (entryHistory input C.val .uncapped accounting actual stage sample).map view), exit) := by
    apply Prod.ext
    · exact overlayEventualStageExit_prior P fee hfee C accounting source stage sample
    · rfl
  rw [hrv]
  exact h

variable [MeasurableSpace Seed]

/-- Last-cursor joint-law restriction from the current entry law and
the actual minimal capture. The source tail guard is discharged by the
proved full exit law, with no source reachability condition. -/
theorem overlay_finalCursorLaw_of_entryLaw_and_minimal_capture
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hlast : stage.val + 1 = P.sharedInstance.stageCount)
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
      (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage)
    (hcapture : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν),
      OverlayMinimalExitCaptured P fee hfee C accounting source.rule stage sample) :
    (((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map (fun sample =>
      (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (overlayRule P fee hfee source.rule)
        (overlayData P source.rule).toRecordSimulatorData sample))).restrict
          (completedCursorCell P.sharedInstance Seed P.sharedInstance.stageCount) =
    (((P.input 0 (by norm_num)).seededWorldLaw ν).map (fun sample =>
      (sample.1, completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample))).restrict
        (completedCursorCell P.sharedInstance Seed P.sharedInstance.stageCount) := by
  let μa := (P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)
  let μs := (P.input 0 (by norm_num)).seededWorldLaw ν
  let completeA := fun sample : OverlaySeed P Seed × (P.input fee hfee).World =>
    (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (overlayRule P fee hfee source.rule)
      (overlayData P source.rule).toRecordSimulatorData sample)
  let completeS := fun sample : Seed × (P.input 0 (by norm_num)).World =>
    (sample.1, completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule sample)
  let exitA := overlayEventualStageExit P fee hfee C accounting source.rule stage
  let exitS := sourceEventualStageExitSome P 0 (by norm_num) C accounting source stage
  let project := finalCursorTailProjection P.sharedInstance.stageCount source.rule
  have hcA : Measurable completeA := (measurable_fst.comp measurable_fst).prodMk
    (measurable_overlayShadowCompletedHistory P fee hfee C accounting source.rule source.measurable_rule)
  have hcS : Measurable completeS := measurable_fst.prodMk
    (measurable_completedHistory (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule source.measurable_rule)
  have heA : Measurable exitA := measurable_overlayEventualStageExit P fee hfee C accounting source.rule source.measurable_rule stage
  have heS : Measurable exitS := measurable_sourceEventualStageExitSome P 0 (by norm_num) C accounting source stage
  have hp : Measurable project := measurable_finalCursorTailProjection _ source.rule source.measurable_rule
  have hcapA : ∀ᵐ sample ∂μa,
      cursorCompletedNatProjection P.sharedInstance.stageCount (completeA sample) = project (exitA sample) := by
    filter_upwards [hcapture, overlayEventualStageExit_tailAllowed_ae_of_entryLaw P fee hfee C accounting
      source ν stage hfinite hentry] with sample hc ht
    exact overlay_finalCursorTail_capture_of_minimal_exit P fee hfee C accounting source.rule stage hlast sample hc ht
  have hcapS := source_finalCursorCapture_ae P 0 (by norm_num) C accounting source ν stage hlast hfinite
  have hA : (μa.map completeA).map (cursorCompletedNatProjection P.sharedInstance.stageCount) =
      (μa.map exitA).map project := by
    rw [Measure.map_map (measurable_cursorCompletedNatProjection _) hcA, Measure.map_map hp heA]
    exact Measure.map_congr hcapA
  have hS : (μs.map completeS).map (cursorCompletedNatProjection P.sharedInstance.stageCount) =
      (μs.map exitS).map project := by
    rw [Measure.map_map (measurable_cursorCompletedNatProjection _) hcS, Measure.map_map hp heS]
    exact Measure.map_congr hcapS
  have hexit : μa.map exitA = μs.map exitS :=
    overlayEventualStageExit_law_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry
  apply completedCursor_restrict_eq_of_natProjectionLaw _ _ P.sharedInstance.stageCount
  exact hA.trans ((congrArg (fun ρ => ρ.map project) hexit).trans hS.symm)

/-- Exact original SourceHistoryLaw from actual all-entry laws and
actual minimal stage captures, with all terminal cursors and branches.
Positive stage count is derived from the original certificate. -/
theorem overlaySourceHistoryLaw_of_entryLaws_and_minimal_captures
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ∀ stage : P.sharedInstance.Stage,
      ((P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν)).map
        (overlayVirtualEntryGate P fee hfee C accounting source.rule stage) =
          sourceEventualEntrySeedLaw P 0 (by norm_num) C accounting source ν stage)
    (hcapture : ∀ stage : P.sharedInstance.Stage,
      ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw (overlaySeedLaw P fee hfee ν),
        OverlayMinimalExitCaptured P fee hfee C accounting source.rule stage sample) :
    P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting ν (overlaySeedLaw P fee hfee ν) source.rule
      (overlayRule P fee hfee source.rule) (overlayData P source.rule).toRecordSimulatorData := by
  apply overlaySourceHistoryLaw_of_cursor_restrictions P fee hfee C accounting source ν hfinite
  intro cursor
  by_cases hc : cursor.val < P.sharedInstance.stageCount
  · let stage : P.sharedInstance.Stage := ⟨cursor.val, hc⟩
    exact overlay_completedCursorLaw_of_entryLaw_and_capture P fee hfee C accounting source ν stage hfinite (hentry stage)
      ((hcapture stage).mono (fun sample h => overlay_terminalCapture_of_minimal_exit P fee hfee C accounting source.rule stage sample h))
  · have hN : cursor.val = P.sharedInstance.stageCount := by have hb := cursor.isLt; omega
    have hpos : 0 < P.sharedInstance.stageCount := by rw [P.stageCount_eq]; exact P.certificate.stages_pos
    let stage : P.sharedInstance.Stage := ⟨P.sharedInstance.stageCount - 1, by
      change P.sharedInstance.stageCount - 1 < P.sharedInstance.stageCount
      omega⟩
    have hlast : stage.val + 1 = P.sharedInstance.stageCount := by dsimp only [stage]; omega
    rw [hN]
    exact overlay_finalCursorLaw_of_entryLaw_and_minimal_capture P fee hfee C accounting source ν stage hlast hfinite
      (hentry stage) (hcapture stage)

end PDROC
