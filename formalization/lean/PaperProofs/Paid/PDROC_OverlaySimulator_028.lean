module

public import PaperProofs.Paid.PDROC_OverlaySimulator_026
public import PaperProofs.Paid.PDROC_OverlaySimulator_027

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem overlay_optionWrite_reserial {I : Instance} (history : List (VisibleEvent I)) (action : Action I) :
    optionWriteBit (reserialAction history (fun _ bit => bit) action) = optionWriteBit action := by
  cases action <;> rfl

/-- A guarded actual write necessarily came from a writing auxiliary record;
the abandonment fallback cannot create an ordinary write. -/
theorem overlay_rule_write_record (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) (bit : Bool)
    (hh : historyHalted history = false) (hc : historyCursor history = stage.val)
    (hw : historyWritten history stage = none) (haction : overlayRule P fee hfee source seed history = .write stage bit) :
    ∃ (draw : SimulatorDraw P.sharedInstance) (decision : Bool),
      overlaySeedDraw P source seed stage (overlayShadow P source seed history) = some draw ∧
        draw.record.decision = some decision := by
  have hcan : overlayCandidate P fee hfee source seed history = .write stage bit := by
    unfold overlayRule at haction
    dsimp only at haction
    split at haction
    · exact haction
    · cases haction
  rw [overlayCandidate_prewrite P fee hfee source seed history stage hh hc hw] at hcan
  cases hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed history) with
  | none => simp only [hdraw, overlayDrawAction, reduceCtorEq] at hcan
  | some draw =>
    cases hd : draw.record.decision with
    | none =>
      have hnone : optionWriteBit draw.action = none :=
        (overlaySeedDraw_some_spec P source seed stage _ draw hdraw).1.symm.trans hd
      have hcan' : reserialAction history (fun _ bit => bit) draw.action = .write stage bit := by
        simpa only [hdraw, overlayDrawAction, hd] using hcan
      have hb := congrArg optionWriteBit hcan'
      rw [overlay_optionWrite_reserial] at hb
      rw [hnone] at hb
      cases hb
    | some decision => exact ⟨draw, decision, rfl, hd⟩

/-- The full virtual entry stays unchanged through the actual current-port
reviews, on EVERY path. This is not an almost-sure or finite-test claim. -/
theorem overlay_prewrite_shadow_eq_entry (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage sample = some entry)
    (n : ℕ)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).halted = false)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage = none) :
    overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history =
      overlayShadow P source sample.1 entry := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  obtain ⟨start, hs, hb, hh⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage sample entry).mp he
  have hle : start ≤ n := by
    by_contra h
    exact hb n (lt_of_not_ge h) hc
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  have he' : FirstEntryAt input C.val .uncapped accounting actual stage.val start sample := ⟨hs, hb⟩
  have hhistory := overlay_prewrite_history_eq_reviews P fee hfee C accounting actual
    (overlayRule_legal P fee hfee C accounting source) sample start stage he' extra ha hw
  have hword : headReviewHistory (P.input fee hfee) stage (worldTapes (P.input fee hfee) sample.2 stage) extra =
      (List.ofFn (fun k : Fin extra => worldTapes (P.input fee hfee) sample.2 stage k.val)).map
        (fun symbol => .observation stage symbol.val) := by
    simp only [headReviewHistory, List.map_ofFn, Function.comp_def]
  rw [hhistory, hword]
  have happ := overlayShadow_append_observations P source sample.1
    (run input C.val .uncapped accounting actual sample start).history stage
    (List.ofFn (fun k : Fin extra => worldTapes (P.input fee hfee) sample.2 stage k.val))
  exact happ.trans (congrArg (overlayShadow P source sample.1) hh)

/-- Exact record-aware report packet at a genuine actual write. The chosen
record is identified with the ORIGINAL actual entry's record, with no
source-history law, fresh-law, return or finite-ET input. -/
theorem overlay_write_report_packet (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage sample = some entry)
    (n : ℕ) (bit : Bool)
    (ha : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).halted = false)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).cursor = stage.val)
    (hw : (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).ledger.written stage = none)
    (hact : overlayRule P fee hfee source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history = .write stage bit) :
    let record := (overlayData P source).record sample.1 stage entry
    ∃ decision : Bool, record.decision = some decision ∧
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (n + 1)).ledger.written stage = some bit ∧
      reportedWriteError (overlayShadow P source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (n + 1)).history) stage =
        some ((bit != (P.input fee hfee).truthAt sample.2 stage) || overlaySeedMark P sample.1 stage record) ∧
      (historyReport (overlayShadow P source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (n + 1)).history) stage).map Prod.fst =
        some (overlayReportTruth bit decision ((P.input fee hfee).truthAt sample.2 stage)
          (overlaySeedMark P sample.1 stage record)) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let cur := run input C.val .uncapped accounting actual sample n
  have hl := overlayRule_legal P fee hfee C accounting source
  have hp := run_prefix_of_active input C.val .uncapped accounting actual hl sample n ha
  have hhh := (prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ hp).trans ha
  have hhc := (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp).trans hc
  have hhw := (prefix_historyWritten input C.val .uncapped accounting actual sample.1 _ _ hp stage).trans hw
  obtain ⟨draw, decision, hd, hdecision⟩ := overlay_rule_write_record P fee hfee source sample.1 cur.history stage bit hhh hhc hhw hact
  have hshadow := overlay_prewrite_shadow_eq_entry P fee hfee C accounting source sample stage entry he n ha hc hw
  have hrecord : (overlayData P source).record sample.1 stage entry = draw.record := by
    change simulatorDrawRecord (overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry)) = _
    rw [← hshadow, hd]
    rfl
  have hrec : simulatorDrawRecord (overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 cur.history)) = draw.record := by
    rw [hd]
    rfl
  have hd' : (simulatorDrawRecord (overlaySeedDraw P source sample.1 stage
      (overlayReplay (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1 cur.history).shadow)).decision = some decision := by
    change (simulatorDrawRecord (overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 cur.history))).decision = _
    rw [hrec]
    exact hdecision
  have hrec' : simulatorDrawRecord (overlaySeedDraw P source sample.1 stage
      (overlayReplay (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) sample.1 cur.history).shadow) = draw.record := by
    change simulatorDrawRecord (overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 cur.history)) = _
    exact hrec
  let next := record accounting cur (.write stage bit) (writeResponses C.val cur stage bit)
    (reportedWriteLedger C.val cur stage bit) cur.cursor false
  have hstep : Step input C.val .uncapped accounting (worldTapes input sample.2) cur (.write stage bit) next :=
    .write cur stage bit ⟨ha, hc⟩ hw (Or.inl rfl)
  have hact' : actual sample.1 cur.history = .write stage bit := hact
  have hnext := run_succ_of_step input C.val .uncapped accounting actual sample n next ha (by change Step input C.val .uncapped accounting _ cur (actual sample.1 cur.history) next; rw [hact']; exact hstep)
  have ht : cur.ledger.truth stage = input.truthAt sample.2 stage :=
    congrFun (run_truth input C.val .uncapped accounting actual hl sample n) stage
  refine ⟨decision, by rw [hrecord]; exact hdecision, ?_, ?_, ?_⟩
  · rw [hnext]
    simp only [next, record, reportedWriteLedger, C.property.1.1, ite_true, writeLedger, Function.update_self]
  · have hresult := overlayReplay_writeReport_error (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)
      sample.1 cur.history stage bit (cur.ledger.truth stage) cur.clock decision hd'
    rw [hnext]
    simpa only [next, record, writeResponses, C.property.1.1, ite_true, writeLedger, List.singleton_append,
      overlayShadow, overlaySeedReplay, hrec', hrecord, ht] using hresult
  · have hresult := overlayReplay_writeReport_report (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)
      sample.1 cur.history stage bit (cur.ledger.truth stage) cur.clock decision hd'
    have hfirst := congrArg (fun value => value.map Prod.fst) hresult
    rw [hnext]
    simpa only [next, record, writeResponses, C.property.1.1, ite_true, writeLedger, List.singleton_append,
      overlayShadow, overlaySeedReplay, hrec', hrecord, ht, Option.map_some] using hfirst

end PDROC
