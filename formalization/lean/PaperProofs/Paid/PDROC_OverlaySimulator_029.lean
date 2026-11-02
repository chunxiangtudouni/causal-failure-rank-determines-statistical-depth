module

public import PaperProofs.Paid.PDROC_OverlaySimulator_028
public import PaperProofs.Paid.PDROC_OverlaySimulator_022
public import PaperProofs.Common.ReferenceMassFlow
public import PaperProofs.Common.ReferenceGlobalCost

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem overlay_actual_report_written (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (n : ℕ) (stage : P.sharedInstance.Stage)
    (hr : (historyReport (run (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) sample n).history stage).isSome = true) :
    ∃ bit, (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage = some bit := by
  obtain ⟨k, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
    (overlayRule_legal P fee hfee C accounting source) sample n
  have hr' := prefix_historyReport_early (P.input fee hfee) C.val C.property.1.1 .uncapped accounting
    (overlayRule P fee hfee source) sample.1 _ _ hp stage
  rw [hr'] at hr
  cases ht : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.reportTime stage with
  | none => simp only [ht, Option.map_none, Option.isSome_none, Bool.false_eq_true] at hr
  | some time =>
    have hn := (prefix_invariant (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
      sample.1 _ _ hp).report_written stage time ht
    cases hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage with
    | none => exact (hn hw).elim
    | some bit => exact ⟨bit, rfl⟩

theorem overlay_virtual_error_written (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (n : ℕ) (stage : P.sharedInstance.Stage)
    (hr : reportedWriteError (overlayShadow P source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history) stage = some true) :
    ∃ bit, (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage = some bit := by
  obtain ⟨k, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
    (overlayRule_legal P fee hfee C accounting source) sample n
  cases hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage with
  | some bit => exact ⟨bit, rfl⟩
  | none =>
    have ha := (prefix_historyWritten (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
      sample.1 _ _ hp stage).trans hw
    have hv := ((overlayReplay_historyProjection (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)
      sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history).2.1 stage).mp ha
    have hwrite : historyWrite (overlayShadow P source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history) stage = none := by
      cases hh : historyWrite (overlayShadow P source sample.1
          (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history) stage with
      | none => rfl
      | some pair =>
        change historyWritten (overlayShadow P source sample.1
          (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history) stage = none at hv
        simp only [historyWritten, hh, Option.map_some, reduceCtorEq] at hv
    unfold reportedWriteError at hr
    rw [hwrite] at hr
    change (none : Option Bool) = some true at hr
    cases hr

theorem overlay_written_shadow_frames (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (a b : ℕ) (ba bb : Bool)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample a).ledger.written stage = some ba)
    (hb : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample b).ledger.written stage = some bb) :
    reportedWriteError (overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample b).history) stage =
        reportedWriteError (overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample a).history) stage ∧
      historyReport (overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample b).history) stage =
        historyReport (overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample a).history) stage := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  rcases le_total a b with h | h
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨run_overlay_reportedWriteError_frame input C.val C.property.1.1 .uncapped accounting actual hl sample
      (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1 a extra stage ba ha,
      run_overlay_written_report_frame input C.val C.property.1.1 .uncapped accounting actual hl sample
        (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1 a extra stage ba ha⟩
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨(run_overlay_reportedWriteError_frame input C.val C.property.1.1 .uncapped accounting actual hl sample
      (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1 b extra stage bb hb).symm,
      (run_overlay_written_report_frame input C.val C.property.1.1 .uncapped accounting actual hl sample
        (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1 b extra stage bb hb).symm⟩

theorem overlay_virtual_error_at_written (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (n : ℕ) (bit : Bool)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage = some bit) :
    P.virtualWriteError fee hfee C accounting (overlayRule P fee hfee source) (overlayData P source).toRecordSimulatorData stage sample ↔
      reportedWriteError (overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history) stage = some true := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨bm, hbm⟩ := overlay_virtual_error_written P fee hfee C accounting source sample m stage hm
    exact (overlay_written_shadow_frames P fee hfee C accounting source sample stage n m bit bm hw hbm).1.symm.trans hm
  · intro hn
    exact ⟨n, hn⟩

section WithMeasure
variable [MeasurableSpace Seed]

/-- Every actual ordinary write has a finite genuine write/report packet
whose selected record is the exact original actual-entry record. -/
theorem overlay_ordinary_packet_witness (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (bit : Bool)
    (hd : P.actualOrdinaryDecision fee hfee C .uncapped accounting (overlayRule P fee hfee source) sample stage = some bit) :
    ∃ (entry : List (VisibleEvent P.sharedInstance)) (clock : ℕ) (decision : Bool),
      entryHistory (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage sample = some entry ∧
      ((overlayData P source).record sample.1 stage entry).decision = some decision ∧
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample clock).ledger.written stage = some bit ∧
      reportedWriteError (overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample clock).history) stage =
        some ((bit != (P.input fee hfee).truthAt sample.2 stage) || overlaySeedMark P sample.1 stage ((overlayData P source).record sample.1 stage entry)) ∧
      (historyReport (overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample clock).history) stage).map Prod.fst =
        some (overlayReportTruth bit decision ((P.input fee hfee).truthAt sample.2 stage)
          (overlaySeedMark P sample.1 stage ((overlayData P source).record sample.1 stage entry))) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨n, bit', hn⟩ := overlay_actualOrdinaryDecision_written_exists P fee hfee C .uncapped accounting actual sample stage bit hd
  have hd' := actualOrdinaryDecision_of_written P fee hfee C .uncapped accounting actual hl sample n stage bit' hn
  have hbits : bit' = bit := Option.some.inj (hd'.symm.trans hd)
  subst bit'
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample n
  obtain ⟨beforeClock, old, _, hpold, hactive, haction⟩ := prefix_written_has_write input C.val .uncapped accounting actual sample.1 _ _ hp stage bit hn
  have hold : run input C.val .uncapped accounting actual sample beforeClock = old :=
    prefix_eq_run input C.val .uncapped accounting actual sample.1 _ _ hpold
  obtain ⟨next, hs⟩ := hl sample.1 _ _ beforeClock old hpold hactive
  have hfields : old.cursor = stage.val ∧ old.ledger.written stage = none := by
    change Step input C.val .uncapped accounting _ old (actual sample.1 old.history) next at hs
    rw [haction] at hs
    cases hs with
    | write _ _ live port _ => exact ⟨live.2, port⟩
  have hentry : ∃ entry, entryHistory input C.val .uncapped accounting actual stage sample = some entry := by
    cases he : entryHistory input C.val .uncapped accounting actual stage sample with
    | none =>
      have hlt := run_cursor_lt_of_no_entry input C.val .uncapped accounting actual hl sample stage he beforeClock
      rw [hold, hfields.1] at hlt
      omega
    | some entry => exact ⟨entry, rfl⟩
  obtain ⟨entry, he⟩ := hentry
  obtain ⟨decision, hdecision, hwrite, herror, htruth⟩ := overlay_write_report_packet P fee hfee C accounting source sample stage entry he beforeClock bit
    (by rw [hold]; exact hactive) (by rw [hold]; exact hfields.1) (by rw [hold]; exact hfields.2)
    (by change actual sample.1 (run input C.val .uncapped accounting actual sample beforeClock).history = _; rw [hold]; exact haction)
  exact ⟨entry, beforeClock + 1, decision, he, hdecision, hwrite, herror, htruth⟩

end WithMeasure

end PDROC
