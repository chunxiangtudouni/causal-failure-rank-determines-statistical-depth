module

public import PaperProofs.Paid.PDROC_OverlaySimulator_031
public import PaperProofs.Paid.PDROC_SimulatorLaw_010
public import PaperProofs.Paid.PDROC_Simulator_034

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Full shadow packet at the actual early report, retaining the old review
word, old write and virtual serial. This strengthens the port projections. -/
theorem overlayReplay_writeReport_full {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool)
    (ghost : SimSeed → SimulatorCache I → List (OverlayGhostCall I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (bit truth : Bool) (serial : ℕ) (decision : Bool)
    (hd : (simulatorDrawRecord (draw seed stage (overlayReplay draw mark ghost seed history).shadow)).decision = some decision) :
    let cache := overlayReplay draw mark ghost seed history
    let record0 := simulatorDrawRecord (draw seed stage cache.shadow)
    let virtualSerial := (historyActions cache.shadow).length + record0.observations.length
    (overlayReplay draw mark ghost seed (history ++ [.wrote stage bit serial, .report stage truth serial])).shadow =
      cache.shadow ++ simulatorReviewPacket stage record0 ++
        [.wrote stage decision virtualSerial,
          .report stage (overlayReportTruth bit decision truth (mark seed stage record0)) virtualSerial] := by
  dsimp only
  rw [show history ++ [.wrote stage bit serial, .report stage truth serial] =
    (history ++ [.wrote stage bit serial]) ++ [.report stage truth serial] by simp]
  rw [overlayReplay_append_event, overlayReplay_append_event]
  simp only [overlayStep, simulatorStep, simulatorAppend, Function.update_self, Option.getD_some]
  rw [hd]
  simp [historyWritten, historyWrite, historyWriteSerial,
    List.filterMap_append, eventWrite, List.append_assoc]

universe u
variable {Seed : Type u}

/-- Exact full virtual source terminal packet at the real mixture write.
No probability, source reachability or postwrite guard premise is needed. -/
theorem overlay_mixture_write_fullpacket (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : OverlaySeed P Seed)
    (world : (P.input fee hfee).World) (start : ℕ) (s : State P.sharedInstance)
    (stage : P.sharedInstance.Stage) (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hdraw : overlaySeedDraw P source seed stage (overlayShadow P source seed s.history) = some draw)
    (hd : draw.record.decision = some decision) (haction : draw.action = .write stage decision)
    (n : ℕ) (hs : (P.overlayRecordTest fee hfee draw.record).rule.stop (overlaySeedCoins P seed stage draw.record)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    let bit := (P.overlayRecordTest fee hfee draw.record).rule.decision (overlaySeedCoins P seed stage draw.record)
      (worldTapes (P.input fee hfee) world stage)
    overlayShadow P source seed (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source)
      (seed, world) (start + n + 1)).history =
      sourceDrawTerminalHistory stage (overlayShadow P source seed s.history) draw
        (overlayReportTruth bit decision ((P.input fee hfee).truthAt world stage) (overlaySeedMark P seed stage draw.record)) := by
  dsimp only
  let input := P.input fee hfee
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let bit := (P.overlayRecordTest fee hfee draw.record).rule.decision (overlaySeedCoins P seed stage draw.record) tape
  have hstate := overlayRun_write_at_mixture P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have hshadow : overlayShadow P source seed before.history = overlayShadow P source seed s.history :=
    overlayReviewStateFrom_shadow P fee hfee accounting source seed stage tape s n
  have hrec : simulatorDrawRecord (overlaySeedDraw P source seed stage
      (overlayReplay (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed before.history).shadow) = draw.record := by
    change simulatorDrawRecord (overlaySeedDraw P source seed stage (overlayShadow P source seed before.history)) = _
    rw [hshadow, hdraw]
    rfl
  have ht : before.ledger.truth stage = input.truthAt world stage := by
    rw [show before.ledger.truth = s.ledger.truth from simulatorReviewStateFrom_truth input accounting stage tape s n]
    rw [← hs0]
    exact congrFun (run_truth input C.val .uncapped accounting (overlayRule P fee hfee source)
      (overlayRule_legal P fee hfee C accounting source) (seed, world) start) stage
  have hresult := overlayReplay_writeReport_full (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source)
    seed before.history stage bit (before.ledger.truth stage) before.clock decision (by rw [hrec, hd])
  have hshadowraw : (overlayReplay (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed before.history).shadow =
      (overlayReplay (overlaySeedDraw P source) (overlaySeedMark P) (overlaySeedGhost P source) seed s.history).shadow := hshadow
  dsimp only at hresult
  rw [hrec, hshadowraw, ht] at hresult
  have hhistory : (run input C.val .uncapped accounting (overlayRule P fee hfee source)
      (seed, world) (start + n + 1)).history =
      before.history ++ [.wrote stage bit before.clock, .report stage (before.ledger.truth stage) before.clock] := by
    rw [hstate]
    simp only [record, writeResponses, C.property.1.1, ite_true, writeLedger, List.singleton_append]
    rfl
  rw [hhistory, sourceDrawTerminalHistory_write stage _ draw _ decision haction, ht]
  exact hresult

end PDROC
