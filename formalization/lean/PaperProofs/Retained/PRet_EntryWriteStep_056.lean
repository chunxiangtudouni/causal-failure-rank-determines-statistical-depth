module

public import PaperProofs.Retained.PRet_EntryReviewStep_055

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryWriteStep056

open Common Common.Native PRetInformationPackets006 PRetEntryReplay045
open PRetEntryInvariant050 PRetEntryPacketInvariant054 PRetActualPacketReplay020 PRetShadowAppend014

variable {I : Instance}

theorem write_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (first start oldClock : ℕ) (startup : Startup I) (target next : State (I.freshSuffix first))
    (stage : (I.freshSuffix first).Stage) (bit : Bool) (packets : List (Packet (I.freshSuffix first)))
    (hclock : start ≤ oldClock)
    (hinfo : informationTrace target.history = packets.flatMap Packet.events)
    (hreplay : replayFrom accounting source sample.1 startup (packets.map (liftPacket first)) =
      some (publicStartup (run input C mode accounting source sample oldClock)))
    (hr : target.ledger.reviews = (fun stage =>
      (run input C mode accounting source sample oldClock).ledger.reviews (I.freshStageLift first stage)))
    (hw : target.ledger.written = (fun stage =>
      (run input C mode accounting source sample oldClock).ledger.written (I.freshStageLift first stage)))
    (htruth : target.ledger.truth stage = (run input C mode accounting source sample oldClock).ledger.truth (I.freshStageLift first stage))
    (ha : (run input C mode accounting source sample oldClock).halted = false)
    (hselected : source sample.1 (run input C mode accounting source sample oldClock).history =
      .write (I.freshStageLift first stage) bit)
    (hstep : Step (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first sample.2))
      target (.write stage bit) next) :
    EntryInvariant input C mode accounting source sample first start startup next := by
  let original := run input C mode accounting source sample oldClock
  let packet := Packet.write stage bit (original.ledger.truth (I.freshStageLift first stage))
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting source hlegal sample oldClock
  obtain ⟨sourceNext, hsourceStep⟩ := hlegal sample.1 _ _ m _ hp ha
  have hnext := run_succ_of_step input C mode accounting source sample oldClock sourceNext ha hsourceStep
  rw [hselected] at hsourceStep
  have hresponse : (liftPacket first packet).applyPublic accounting (publicStartup original) =
      publicStartup (run input C mode accounting source sample (oldClock + 1)) := by
    rw [hnext]
    cases hsourceStep
    exact (publicStartup_write_early C hearly accounting original (I.freshStageLift first stage) bit).symm
  obtain ⟨newClock, hnew, hconsume⟩ := consume_actual input C mode accounting source hlegal sample oldClock
    (liftPacket first packet) ha hselected hresponse
  apply entryInvariant_packet input C mode accounting source sample first start oldClock newClock startup target next packets packet
    hclock (Nat.le_of_lt hnew) hreplay hconsume hr hw
  · cases hstep
    change informationTrace (target.history ++ writeResponses (freshContract (I.freshSuffix first)) target stage bit) = _
    rw [informationTrace_append, hinfo]
    dsimp only [packet, original]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, writeResponses, freshContract, ↓reduceIte, informationTrace,
      informationEvent, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      Packet.events, writeLedger]
    rw [htruth]
    rfl
  · cases hstep
    simp only [packet, record, reportedWriteLedger, freshContract, ↓reduceIte, writeLedger,
      Packet.applyPublic, Startup.writePublic, publicStartup]
  · cases hstep
    simp only [packet, record, reportedWriteLedger, freshContract, ↓reduceIte, writeLedger,
      Packet.applyPublic, Startup.writePublic, publicStartup]

end PaperProofs.Retained.PRetEntryWriteStep056

