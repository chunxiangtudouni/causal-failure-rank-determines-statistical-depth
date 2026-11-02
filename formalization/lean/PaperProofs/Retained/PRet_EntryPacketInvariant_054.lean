module

public import PaperProofs.Retained.PRet_EntryInvariant_050
public import PaperProofs.Retained.PRet_LiftedPacketFrames_052
public import PaperProofs.Retained.PRet_EntryReplayAppend_053

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryPacketInvariant054

open Common Common.Native PRetInformationPackets006 PRetPublicAdministrativeReplay005
open PRetEntryReplay045 PRetEntryInvariant050 PRetAdministrativeFrames013
open PRetLiftedPacketFrames052 PRetEntryReplayAppend053

variable {I : Instance}

theorem entryInvariant_frame {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (first start : ℕ) (startup : Startup I)
    (target next : State (I.freshSuffix first))
    (hi : EntryInvariant input C mode accounting source sample first start startup target)
    (hinfo : informationTrace next.history = informationTrace target.history)
    (hr : next.ledger.reviews = target.ledger.reviews)
    (hw : next.ledger.written = target.ledger.written) :
    EntryInvariant input C mode accounting source sample first start startup next := by
  obtain ⟨packets, oldClock, hclock, hpackets, hreplay, hreviews, hwritten⟩ := hi
  exact ⟨packets, oldClock, hclock, hinfo.trans hpackets, hreplay, hr.trans hreviews, hw.trans hwritten⟩

/-- Genuine lifted packet update in the actual entry induction. The two
different real clocks/normal accountings do not alter the review/write
projection; original source administration remains in its public shadow. -/
theorem entryInvariant_packet {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (first start oldClock newClock : ℕ) (startup : Startup I)
    (target next : State (I.freshSuffix first)) (packets : List (Packet (I.freshSuffix first)))
    (packet : Packet (I.freshSuffix first)) (hclock : start ≤ oldClock) (hnew : oldClock ≤ newClock)
    (hreplay : replayFrom accounting source sample.1 startup (packets.map (liftPacket first)) =
      some (publicStartup (run input C mode accounting source sample oldClock)))
    (hconsume : consume accounting source sample.1 (publicStartup (run input C mode accounting source sample oldClock))
      (liftPacket first packet) = some (publicStartup (run input C mode accounting source sample newClock)))
    (hr : target.ledger.reviews = (fun stage =>
      (run input C mode accounting source sample oldClock).ledger.reviews (I.freshStageLift first stage)))
    (hw : target.ledger.written = (fun stage =>
      (run input C mode accounting source sample oldClock).ledger.written (I.freshStageLift first stage)))
    (hinfo : informationTrace next.history = (packets ++ [packet]).flatMap Packet.events)
    (hrNext : next.ledger.reviews =
      (packet.applyPublic (zeroNormalAccounting (I.freshSuffix first)) (publicStartup target)).reviews)
    (hwNext : next.ledger.written =
      (packet.applyPublic (zeroNormalAccounting (I.freshSuffix first)) (publicStartup target)).written) :
    EntryInvariant input C mode accounting source sample first start startup next := by
  have hf : (run input C mode accounting source sample newClock).ledger.reviews =
        ((liftPacket first packet).applyPublic accounting (publicStartup (run input C mode accounting source sample oldClock))).reviews ∧
      (run input C mode accounting source sample newClock).ledger.written =
        ((liftPacket first packet).applyPublic accounting (publicStartup (run input C mode accounting source sample oldClock))).written := by
    unfold consume at hconsume
    split at hconsume
    · have heq := Option.some.inj hconsume
      have hframes := settle_frames accounting source (I.stageCount + 2 * I.toolCount + 2) sample.1
        ((liftPacket first packet).applyPublic accounting (publicStartup (run input C mode accounting source sample oldClock)))
      rw [heq] at hframes
      exact ⟨hframes.1, hframes.2.1⟩
    · cases hconsume
  have hlift := lifted_packet_frames first accounting (zeroNormalAccounting (I.freshSuffix first))
    (publicStartup (run input C mode accounting source sample oldClock)) (publicStartup target) packet hr hw
  refine ⟨packets ++ [packet], newClock, hclock.trans hnew, hinfo,
    replayFrom_extend_lifted first accounting source sample.1 startup packets packet _ _ hreplay hconsume, ?_, ?_⟩
  · exact (hrNext.trans hlift.1).trans (congrArg (fun reviews => reviews ∘ I.freshStageLift first) hf.1.symm)
  · exact (hwNext.trans hlift.2).trans (congrArg (fun written => written ∘ I.freshStageLift first) hf.2.symm)

end PaperProofs.Retained.PRetEntryPacketInvariant054
