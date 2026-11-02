module

public import PaperProofs.Paid.PDROC_OverlayEntry_007
public import PaperProofs.Paid.PDROC_OverlaySimulator_020

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

abbrev OverlayCellGate (P : Parameters) (Seed : Type u) :=
  (Seed × EntryHistory P.sharedInstance) × Option (SimulatorDraw P.sharedInstance)

def overlayRecordCellGateSet (P : Parameters) (record : AuxiliaryRecord)
    (B : Set (Seed × List (VisibleEvent P.sharedInstance))) : Set (OverlayCellGate P Seed) :=
  {gate | ∃ entry, gate.1.2 = some entry ∧ gate.2.map SimulatorDraw.record = some record ∧ (gate.1.1, entry) ∈ B}

theorem measurableSet_overlayRecordCellGateSet [MeasurableSpace Seed] (P : Parameters) (record : AuxiliaryRecord)
    (B : Set (Seed × List (VisibleEvent P.sharedInstance))) (hB : MeasurableSet B) :
    MeasurableSet (overlayRecordCellGateSet P record B) := by
  have hs : overlayRecordCellGateSet P record B = ⋃ entry : List (VisibleEvent P.sharedInstance),
      {gate : OverlayCellGate P Seed | gate.1.2 = some entry} ∩
        {gate | gate.2.map SimulatorDraw.record = some record} ∩ {gate | (gate.1.1, entry) ∈ B} := by
    ext gate
    simp [overlayRecordCellGateSet, and_assoc]
  rw [hs]
  apply MeasurableSet.iUnion
  intro entry
  have he : MeasurableSet {gate : OverlayCellGate P Seed | gate.1.2 = some entry} :=
    (measurableSet_singleton (some entry)).preimage (measurable_snd.comp measurable_fst)
  have hr : MeasurableSet {gate : OverlayCellGate P Seed | gate.2.map SimulatorDraw.record = some record} :=
    (measurableSet_singleton (some record)).preimage
    ((measurable_of_countable (fun draw : Option (SimulatorDraw P.sharedInstance) =>
      draw.map SimulatorDraw.record)).comp measurable_snd)
  exact (he.inter hr).inter (hB.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_const))

theorem overlay_drawRecord_eq_iff_map_some (P : Parameters)
    (draw : Option (SimulatorDraw P.sharedInstance)) (record : AuxiliaryRecord) (decision : Bool)
    (hd : record.decision = some decision) :
    simulatorDrawRecord draw = record ↔ draw.map SimulatorDraw.record = some record := by
  cases draw with
  | none =>
    have hn : simulatorEmptyRecord ≠ record := by
      intro h
      have hh := congrArg AuxiliaryRecord.decision h
      rw [hd] at hh
      cases hh
    simp [simulatorDrawRecord, hn]
  | some draw => simp [simulatorDrawRecord]

/-- The original arbitrary old-seed/full-virtual-entry cell is an exact
preimage of the generated entry/full-draw gate. Writing records cannot be
manufactured from the outer none/default-record branch. -/
theorem overlay_recordCell_eq_gate_preimage (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (record : AuxiliaryRecord) (decision : Bool) (hd : record.decision = some decision)
    (B : Set (Seed × List (VisibleEvent P.sharedInstance))) :
    P.recordCell fee hfee C accounting (overlayRule P fee hfee source)
      (overlayData P source).toRecordSimulatorData stage record B =
      (overlayRecordGate P fee hfee C accounting source stage) ⁻¹' overlayRecordCellGateSet P record B := by
  ext sample
  cases he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) stage sample with
  | none =>
    simp [PaperProofs.Paid.Parameters.recordCell, he, overlayRecordGate, overlayVirtualEntryGate,
      overlayVirtualEntry, overlayCurrentDraw, overlayRecordCellGateSet]
  | some entry =>
    simp [PaperProofs.Paid.Parameters.recordCell, he, overlayRecordGate, overlayVirtualEntryGate,
      overlayVirtualEntry, overlayCurrentDraw, overlayRecordCellGateSet, overlayData,
      overlay_drawRecord_eq_iff_map_some P _ record decision hd, and_comm]

theorem measurableSet_overlay_recordCell [MeasurableSpace Seed]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (source : PolicyRule P.sharedInstance Seed)
    (hm : MeasurableRule source) (stage : P.sharedInstance.Stage)
    (record : AuxiliaryRecord) (decision : Bool) (hd : record.decision = some decision)
    (B : Set (Seed × List (VisibleEvent P.sharedInstance))) (hB : MeasurableSet B) :
    MeasurableSet (P.recordCell fee hfee C accounting (overlayRule P fee hfee source)
      (overlayData P source).toRecordSimulatorData stage record B) := by
  rw [overlay_recordCell_eq_gate_preimage P fee hfee C accounting source stage record decision hd]
  exact (measurableSet_overlayRecordCellGateSet P record B hB).preimage
    (measurable_overlayRecordGate P fee hfee C accounting source hm stage)

end PDROC
