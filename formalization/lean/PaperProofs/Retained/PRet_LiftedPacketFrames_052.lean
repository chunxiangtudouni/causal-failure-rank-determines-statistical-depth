module

public import PaperProofs.Retained.PRet_EntryReplay_045

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetLiftedPacketFrames052

open Common Common.Native PRetInformationPackets006 PRetEntryReplay045

variable {I : Instance}

theorem lifted_packet_frames (first : ℕ) (accounting : NormalAccounting I)
    (targetAccounting : NormalAccounting (I.freshSuffix first))
    (source : Startup I) (target : Startup (I.freshSuffix first)) (packet : Packet (I.freshSuffix first))
    (hr : target.reviews = source.reviews ∘ I.freshStageLift first)
    (hw : target.written = source.written ∘ I.freshStageLift first) :
    (packet.applyPublic targetAccounting target).reviews =
        ((liftPacket first packet).applyPublic accounting source).reviews ∘ I.freshStageLift first ∧
      (packet.applyPublic targetAccounting target).written =
        ((liftPacket first packet).applyPublic accounting source).written ∘ I.freshStageLift first := by
  cases packet with
  | review stage symbol =>
    constructor
    · change Function.update target.reviews stage (target.reviews stage + 1) =
        Function.update source.reviews (I.freshStageLift first stage)
          (source.reviews (I.freshStageLift first stage) + 1) ∘ I.freshStageLift first
      rw [Function.update_comp_eq_of_injective source.reviews
        (StatisticalInput.freshStageLift_injective I first), hr]
      rfl
    · exact hw
  | write stage bit truth =>
    constructor
    · exact hr
    · change Function.update target.written stage (some bit) =
        Function.update source.written (I.freshStageLift first stage) (some bit) ∘ I.freshStageLift first
      rw [Function.update_comp_eq_of_injective source.written
        (StatisticalInput.freshStageLift_injective I first), hw]

theorem liftPacket_events_length (first : ℕ) (packet : Packet (I.freshSuffix first)) :
    (liftPacket first packet).events.length = packet.events.length := by
  cases packet <;> rfl

theorem lifted_packets_information_length (first : ℕ) (packets : List (Packet (I.freshSuffix first))) :
    ((packets.map (liftPacket first)).flatMap Packet.events).length = (packets.flatMap Packet.events).length := by
  induction packets with
  | nil => rfl
  | cons packet later ih =>
    simp only [List.map_cons, List.flatMap_cons, List.length_append, liftPacket_events_length, ih]

end PaperProofs.Retained.PRetLiftedPacketFrames052
