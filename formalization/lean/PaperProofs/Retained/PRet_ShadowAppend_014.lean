module

public import PaperProofs.Retained.PRet_InformationPackets_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetShadowAppend014

open Common Common.Native PRetInformationPackets006

variable {I : Instance}

theorem informationTrace_append (first later : List (VisibleEvent I)) :
    informationTrace (first ++ later) = informationTrace first ++ informationTrace later :=
  List.filterMap_append

theorem informationTrace_packet (packet : Packet I) : informationTrace packet.events = packet.events := by
  cases packet <;> rfl

theorem informationTrace_packets (packets : List (Packet I)) :
    informationTrace (packets.flatMap Packet.events) = packets.flatMap Packet.events := by
  induction packets with
  | nil => rfl
  | cons packet later ih => rw [List.flatMap_cons, informationTrace_append, informationTrace_packet, ih]

theorem shadow_packets {Seed : Type*} (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed)
    (seed : Seed) (packets : List (Packet I)) :
    shadow accounting sourceRule seed (packets.flatMap Packet.events) = replay accounting sourceRule seed packets := by
  unfold shadow
  rw [informationTrace_packets, parse_packets]
  rfl

theorem replay_append {Seed : Type*} (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed)
    (seed : Seed) (first later : List (Packet I)) :
    replay accounting sourceRule seed (first ++ later) =
      (replay accounting sourceRule seed first).bind
        (fun startup => later.foldlM (consume accounting sourceRule seed) startup) := by
  simp only [replay, List.foldlM_append, Option.bind_eq_bind]

theorem replay_append_one {Seed : Type*} (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed)
    (seed : Seed) (packets : List (Packet I)) (packet : Packet I) (startup next : Startup I)
    (hreplay : replay accounting sourceRule seed packets = some startup)
    (hconsume : consume accounting sourceRule seed startup packet = some next) :
    replay accounting sourceRule seed (packets ++ [packet]) = some next := by
  rw [replay_append, hreplay, Option.bind_some]
  change (consume accounting sourceRule seed startup packet).bind (fun final => some final) = some next
  rw [hconsume]
  rfl

/-- The replay update used by an actual delayed review/write. Its public
history may carry different real serials; the hypothesis concerns exactly
the existing serial-normalized R02 informationTrace. -/
theorem shadow_extend_packet {Seed : Type*} (accounting : NormalAccounting I) (sourceRule : PolicyRule I Seed)
    (seed : Seed) (packets : List (Packet I)) (packet : Packet I) (startup next : Startup I)
    (history : List (VisibleEvent I))
    (hinfo : informationTrace history = (packets ++ [packet]).flatMap Packet.events)
    (hreplay : replay accounting sourceRule seed packets = some startup)
    (hconsume : consume accounting sourceRule seed startup packet = some next) :
    shadow accounting sourceRule seed history = some next := by
  unfold shadow
  rw [hinfo, parse_packets]
  change replay accounting sourceRule seed (packets ++ [packet]) = some next
  exact replay_append_one accounting sourceRule seed packets packet startup next hreplay hconsume

end PaperProofs.Retained.PRetShadowAppend014
