module

public import PaperProofs.Paid.PDROC_OverlaySimulator_032

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- A genuine entered writing record reaches its full source terminal
packet after exactly the paid MAP reviews and one real early write. The
witness retains every preceding active current-stage physical clock. -/
theorem overlay_entered_write_packet_clock (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage sample = some entry)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hdraw : overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 entry) = some draw)
    (hd : draw.record.decision = some decision) (haction : draw.action = .write stage decision)
    (hfinite : ∀ (record : AuxiliaryRecord) (coins : Bool × Bool), ∃ n : ℕ,
      (P.overlayRecordTest fee hfee record).rule.stop coins (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞)) :
    let bit := (P.overlayRecordTest fee hfee draw.record).rule.decision (overlaySeedCoins P sample.1 stage draw.record)
      (worldTapes (P.input fee hfee) sample.2 stage)
    ∃ start n : ℕ,
      FirstEntryAt (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) stage.val start sample ∧
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample start).history = entry ∧
      (P.overlayRecordTest fee hfee draw.record).rule.stop (overlaySeedCoins P sample.1 stage draw.record)
        (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞) ∧
      (∀ k ≤ n,
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + k)).halted = false ∧
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + k)).cursor = stage.val) ∧
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + n + 1)).halted = false ∧
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + n + 1)).cursor = stage.val ∧
      (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample (start + n + 1)).ledger.written stage = some bit ∧
      overlayShadow P source sample.1 (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
        sample (start + n + 1)).history =
        sourceDrawTerminalHistory stage (overlayShadow P source sample.1 entry) draw
          (overlayReportTruth bit decision ((P.input fee hfee).truthAt sample.2 stage) (overlaySeedMark P sample.1 stage draw.record)) := by
  dsimp only
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨start, hc, hbefore, hh⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage sample entry).mp he
  let s := run input C.val .uncapped accounting actual sample start
  have he' : FirstEntryAt input C.val .uncapped accounting actual stage.val start sample := ⟨hc, hbefore⟩
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hl sample stage.val start he'
  obtain ⟨hw, hr⟩ := hunborn stage le_rfl
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample start
  have ho : historyObservations s.history stage = [] := by
    have hlen := prefix_historyObservations_length input C.val .uncapped accounting actual sample.1 _ _ hp stage
    rw [hr] at hlen
    exact List.length_eq_zero_iff.mp (ENat.natCast_inj.mp hlen)
  have hdraw0 : overlaySeedDraw P source sample.1 stage (overlayShadow P source sample.1 s.history) = some draw := by
    rw [show s.history = entry from hh]
    exact hdraw
  obtain ⟨n, hs⟩ := hfinite draw.record (overlaySeedCoins P sample.1 stage draw.record)
  have hstate := overlayRun_write_at_mixture P fee hfee C accounting source sample.1 sample.2 start s stage draw decision
    rfl ha hc hw hr ho hdraw0 hd n hs
  have hpacket := overlay_mixture_write_fullpacket P fee hfee C accounting source sample.1 sample.2 start s stage draw decision
    rfl ha hc hw hr ho hdraw0 hd haction n hs
  refine ⟨start, n, he', hh, hs, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : (j : ℕ∞) ≤ (P.overlayRecordTest fee hfee draw.record).rule.stop (overlaySeedCoins P sample.1 stage draw.record)
        (worldTapes input sample.2 stage) := by rw [hs]; exact_mod_cast hj
    have hrun := overlayRun_eq_reviewStateFrom P fee hfee C accounting source sample.1 sample.2 start stage draw decision
      ha hc hw hr ho hdraw0 hd j hj'
    rw [hrun]
    exact ⟨simulatorReviewStateFrom_active input accounting stage _ s j ha,
      (simulatorReviewStateFrom_cursor input accounting stage _ s j).trans hc⟩
  · rw [hstate]; rfl
  · rw [hstate]
    exact (simulatorReviewStateFrom_cursor input accounting stage _ s n).trans hc
  · rw [hstate]
    simp only [record, reportedWriteLedger, C.property.1.1, ite_true, writeLedger, Function.update_self]
  · rw [show s.history = entry from hh] at hpacket
    exact hpacket

end PDROC
