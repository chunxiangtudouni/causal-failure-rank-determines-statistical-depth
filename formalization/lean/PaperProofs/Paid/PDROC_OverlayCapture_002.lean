module

public import PaperProofs.Paid.PDROC_OverlayCapture_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- The RV truth is exactly the transducer's report truth at the selected
record, with the genuine local decision and selected mark. -/
theorem overlayRowVirtualTruth_eq_reportTruth
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (record : AuxiliaryRecord)
    (truth : Bool) (row : OverlayStageCoins) (tape : P.experiment.Tape)
    (decision : Bool) (hd : record.decision = some decision) :
    overlayRowVirtualTruth P fee hfee record truth (row, tape) =
      overlayReportTruth ((P.overlayRecordTest fee hfee record).rule.decision (row.1 record) tape)
        decision truth (row.2 record) := by
  unfold overlayRowVirtualTruth overlayLocalVirtualTruth overlayRowExperimentSample overlayReportTruth
  rw [hd]
  rfl

theorem overlaySeedRowVirtualTruth_eq_reportTruth
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (seed : OverlaySeed P Seed)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) (truth : Bool)
    (tape : P.experiment.Tape) (decision : Bool) (hd : record.decision = some decision) :
    overlayRowVirtualTruth P fee hfee record truth (seed.2.2 stage, tape) =
      overlayReportTruth ((P.overlayRecordTest fee hfee record).rule.decision
        (overlaySeedCoins P seed stage record) tape) decision truth (overlaySeedMark P seed stage record) :=
  overlayRowVirtualTruth_eq_reportTruth P fee hfee record truth (seed.2.2 stage) tape decision hd


theorem overlayEventualStageExit_postwrite_of_entry_draw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) stage sample = some entry)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry) = some draw) :
    (overlayEventualStageExit P fee hfee C accounting source stage sample).2 =
      some (postwriteStageTrace source sample.1.1 stage
        (sourceDrawTerminalHistory stage (overlayShadow P source sample.1 entry) draw
          (overlayRowVirtualTruth P fee hfee draw.record ((P.input fee hfee).truthAt sample.2 stage)
            (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage))) 3) := by
  rw [overlayEventualStageExit_of_entry_draw P fee hfee C accounting source stage sample entry he draw hd]
  rfl

/-- A single concrete draw supplies both the source guard and the exact
whole exit RV on the actual full virtual entry. All action branches remain. -/
theorem overlay_entry_capture_of_eventualReportedDraw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (hgood : optionalSourceDrawGuardGood (sourceForOptionalHistory source) stage
      (overlayEventualReportedDraw P fee hfee C accounting source stage sample)) :
    ∀ entry, entryHistory (P.input fee hfee) C.val .uncapped accounting
        (overlayRule P fee hfee source) stage sample = some entry →
      ∃ draw : SimulatorDraw P.sharedInstance,
        overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry) = some draw ∧
        sourceDrawGuardGood source stage
          (((sample.1.1, overlayShadow P source sample.1 entry), draw),
            overlayRowVirtualTruth P fee hfee draw.record ((P.input fee hfee).truthAt sample.2 stage)
              (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage)) ∧
        (overlayEventualStageExit P fee hfee C accounting source stage sample).2 =
          some (postwriteStageTrace source sample.1.1 stage
            (sourceDrawTerminalHistory stage (overlayShadow P source sample.1 entry) draw
              (overlayRowVirtualTruth P fee hfee draw.record ((P.input fee hfee).truthAt sample.2 stage)
                (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage))) 3) := by
  intro entry he
  obtain ⟨draw, hd, hg⟩ := overlay_entry_drawGood_of_eventualReportedDraw P fee hfee C accounting source stage sample hgood entry he
  exact ⟨draw, hd, hg, overlayEventualStageExit_postwrite_of_entry_draw P fee hfee C accounting source stage sample entry he draw hd⟩

/-- Writing branch normalized to the exact same full initial packet used
by Native 032, including its virtual write/report version serial. -/
theorem overlayEventualStageExit_write_packet
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) stage sample = some entry)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry) = some draw)
    (decision : Bool) (hdecision : draw.record.decision = some decision)
    (haction : draw.action = .write stage decision) :
    let virtualTruth := overlayReportTruth ((P.overlayRecordTest fee hfee draw.record).rule.decision
      (overlaySeedCoins P sample.1 stage draw.record) (worldTapes (P.input fee hfee) sample.2 stage))
      decision ((P.input fee hfee).truthAt sample.2 stage) (overlaySeedMark P sample.1 stage draw.record)
    let serial := (historyActions (overlayShadow P source sample.1 entry)).length + draw.record.observations.length
    (overlayEventualStageExit P fee hfee C accounting source stage sample).2 =
      some (postwriteStageTrace source sample.1.1 stage
        (overlayShadow P source sample.1 entry ++ simulatorReviewPacket stage draw.record ++
          [.wrote stage decision serial, .report stage virtualTruth serial]) 3) := by
  dsimp only
  rw [overlayEventualStageExit_postwrite_of_entry_draw P fee hfee C accounting source stage sample entry he draw hd]
  erw [overlaySeedRowVirtualTruth_eq_reportTruth P fee hfee sample.1 stage draw.record
    ((P.input fee hfee).truthAt sample.2 stage) (worldTapes (P.input fee hfee) sample.2 stage) decision hdecision,
    sourceDrawTerminalHistory_write stage _ draw _ decision haction]

/-- Writing source guard on that very same packet. -/
theorem overlay_entry_guard_write_packet
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (seed : OverlaySeed P Seed) (entry : List (VisibleEvent P.sharedInstance))
    (draw : SimulatorDraw P.sharedInstance) (truth : Bool) (tape : P.experiment.Tape)
    (hgood : sourceDrawGuardGood source stage
      (((seed.1, overlayShadow P source seed entry), draw),
        overlayRowVirtualTruth P fee hfee draw.record truth (seed.2.2 stage, tape)))
    (decision : Bool) (hdecision : draw.record.decision = some decision)
    (haction : draw.action = .write stage decision) :
    let virtualTruth := overlayReportTruth ((P.overlayRecordTest fee hfee draw.record).rule.decision
      (overlaySeedCoins P seed stage draw.record) tape) decision truth (overlaySeedMark P seed stage draw.record)
    let serial := (historyActions (overlayShadow P source seed entry)).length + draw.record.observations.length
    sourcePostwriteGuardGood source seed.1 stage
      (overlayShadow P source seed entry ++ simulatorReviewPacket stage draw.record ++
        [.wrote stage decision serial, .report stage virtualTruth serial]) := by
  dsimp only
  have hg := hgood.2
  rw [overlaySeedRowVirtualTruth_eq_reportTruth P fee hfee seed stage draw.record truth tape decision hdecision,
    sourceDrawTerminalHistory_write stage _ draw _ decision haction] at hg
  exact hg

theorem overlayEventualStageExit_stop_packet
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) stage sample = some entry)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry) = some draw)
    (haction : draw.action = .stop) :
    (overlayEventualStageExit P fee hfee C accounting source stage sample).2 =
      some (overlayShadow P source sample.1 entry ++ simulatorReviewPacket stage draw.record ++ [.stopped]) := by
  rw [overlayEventualStageExit_postwrite_of_entry_draw P fee hfee C accounting source stage sample entry he draw hd]
  have hh := sourceDrawTerminalHistory_halted stage (overlayShadow P source sample.1 entry) draw
    (overlayRowVirtualTruth P fee hfee draw.record ((P.input fee hfee).truthAt sample.2 stage)
      (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage)) (Or.inl haction)
  rw [postwriteStageTrace_of_halted sample.1.1 stage _ hh 3,
    sourceDrawTerminalHistory_stop stage _ draw _ haction]

theorem overlayEventualStageExit_abandon_packet
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) stage sample = some entry)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry) = some draw)
    (haction : draw.action = .abandon) :
    (overlayEventualStageExit P fee hfee C accounting source stage sample).2 =
      some (overlayShadow P source sample.1 entry ++ simulatorReviewPacket stage draw.record ++ [.abandoned]) := by
  rw [overlayEventualStageExit_postwrite_of_entry_draw P fee hfee C accounting source stage sample entry he draw hd]
  have hh := sourceDrawTerminalHistory_halted stage (overlayShadow P source sample.1 entry) draw
    (overlayRowVirtualTruth P fee hfee draw.record ((P.input fee hfee).truthAt sample.2 stage)
      (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage)) (Or.inr haction)
  rw [postwriteStageTrace_of_halted sample.1.1 stage _ hh 3,
    sourceDrawTerminalHistory_abandon stage _ draw _ haction]

end PDROC
