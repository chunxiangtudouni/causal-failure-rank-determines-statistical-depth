module

public import PaperProofs.Retained.PRet_EntryReplay_045

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryReplayAppend053

open Common Common.Native PRetInformationPackets006 PRetEntryReplay045

variable {I : Instance}

theorem replayFrom_append {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup : Startup I) (first later : List (Packet I)) :
    replayFrom accounting source seed startup (first ++ later) =
      (replayFrom accounting source seed startup first).bind
        (fun cached => later.foldlM (consume accounting source seed) cached) := by
  simp only [replayFrom, List.foldlM_append, Option.bind_eq_bind]

theorem replayFrom_append_one {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup : Startup I) (packets : List (Packet I)) (packet : Packet I) (cached next : Startup I)
    (hr : replayFrom accounting source seed startup packets = some cached)
    (hc : consume accounting source seed cached packet = some next) :
    replayFrom accounting source seed startup (packets ++ [packet]) = some next := by
  rw [replayFrom_append, hr, Option.bind_some]
  change (consume accounting source seed cached packet).bind (fun final => some final) = some next
  rw [hc]
  rfl

theorem replayFrom_extend_lifted {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup : Startup I) (packets : List (Packet (I.freshSuffix first)))
    (packet : Packet (I.freshSuffix first)) (cached next : Startup I)
    (hr : replayFrom accounting source seed startup (packets.map (liftPacket first)) = some cached)
    (hc : consume accounting source seed cached (liftPacket first packet) = some next) :
    replayFrom accounting source seed startup ((packets ++ [packet]).map (liftPacket first)) = some next := by
  rw [List.map_append, List.map_singleton]
  exact replayFrom_append_one accounting source seed startup _ _ cached next hr hc

theorem shadowFrom_congr {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup : Startup I) (before later : List (VisibleEvent (I.freshSuffix first)))
    (hinfo : informationTrace before = informationTrace later) :
    shadowFrom first accounting source startup seed before = shadowFrom first accounting source startup seed later := by
  unfold shadowFrom
  rw [hinfo]

end PaperProofs.Retained.PRetEntryReplayAppend053
