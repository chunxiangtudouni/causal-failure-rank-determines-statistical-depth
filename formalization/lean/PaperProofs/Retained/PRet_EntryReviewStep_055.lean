module

public import PaperProofs.Retained.PRet_EntryPacketInvariant_054
public import PaperProofs.Retained.PRet_ActualPacketReplay_020
public import PaperProofs.Retained.PRet_ShadowAppend_014
public import PaperProofs.Common.HistorySuffixTransport

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryReviewStep055

open Common Common.Native PRetInformationPackets006 PRetEntryReplay045
open PRetEntryInvariant050 PRetEntryPacketInvariant054 PRetActualPacketReplay020 PRetShadowAppend014

variable {I : Instance}

theorem review_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (first start oldClock : ℕ) (startup : Startup I) (target next : State (I.freshSuffix first))
    (stage : (I.freshSuffix first).Stage) (packets : List (Packet (I.freshSuffix first)))
    (hclock : start ≤ oldClock)
    (hinfo : informationTrace target.history = packets.flatMap Packet.events)
    (hreplay : replayFrom accounting source sample.1 startup (packets.map (liftPacket first)) =
      some (publicStartup (run input C mode accounting source sample oldClock)))
    (hr : target.ledger.reviews = (fun stage =>
      (run input C mode accounting source sample oldClock).ledger.reviews (I.freshStageLift first stage)))
    (hw : target.ledger.written = (fun stage =>
      (run input C mode accounting source sample oldClock).ledger.written (I.freshStageLift first stage)))
    (ha : (run input C mode accounting source sample oldClock).halted = false)
    (hselected : source sample.1 (run input C mode accounting source sample oldClock).history =
      .review (I.freshStageLift first stage))
    (hstep : Step (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first sample.2))
      target (.review stage) next) :
    EntryInvariant input C mode accounting source sample first start startup next := by
  let original := run input C mode accounting source sample oldClock
  let letter := (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first sample.2)
    stage (target.ledger.reviews stage).toNat).val
  let packet := Packet.review stage letter
  have hcount : target.ledger.reviews stage = original.ledger.reviews (I.freshStageLift first stage) := congrFun hr stage
  have hletter : letter = (worldTapes input sample.2 (I.freshStageLift first stage)
      (original.ledger.reviews (I.freshStageLift first stage)).toNat).val := by
    dsimp only [letter]
    rw [hcount]
    exact restrictFreshWorld_letter input first sample.2 stage _
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting source hlegal sample oldClock
  obtain ⟨sourceNext, hsourceStep⟩ := hlegal sample.1 _ _ m _ hp ha
  have hnext := run_succ_of_step input C mode accounting source sample oldClock sourceNext ha hsourceStep
  rw [hselected] at hsourceStep
  have hresponse : (liftPacket first packet).applyPublic accounting (publicStartup original) =
      publicStartup (run input C mode accounting source sample (oldClock + 1)) := by
    rw [hnext]
    cases hsourceStep
    change (publicStartup original).reviewPublic accounting (I.freshStageLift first stage) letter = _
    rw [hletter]
    rfl
  obtain ⟨newClock, hnew, hconsume⟩ := consume_actual input C mode accounting source hlegal sample oldClock
    (liftPacket first packet) ha hselected hresponse
  apply entryInvariant_packet input C mode accounting source sample first start oldClock newClock startup target next packets packet
    hclock (Nat.le_of_lt hnew) hreplay hconsume hr hw
  · cases hstep
    change informationTrace (target.history ++ [.observation stage letter]) = _
    rw [informationTrace_append, hinfo]
    change packets.flatMap Packet.events ++ [.observation stage letter] = _
    rw [List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  · cases hstep
    rfl
  · cases hstep
    rfl

end PaperProofs.Retained.PRetEntryReviewStep055
