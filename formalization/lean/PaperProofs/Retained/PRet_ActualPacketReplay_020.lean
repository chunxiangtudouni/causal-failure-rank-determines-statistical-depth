module

public import PaperProofs.Retained.PRet_ReplayInvariant_016
public import PaperProofs.Retained.PRet_ShadowAppend_014
public import PaperProofs.Retained.PRet_ExecutionPrefixes_018

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetActualPacketReplay020

open Common Common.Native PRetPublicAdministrativeReplay005 PRetInformationPackets006
open PRetExactTerminal001 PRetAdministrativeFrames013 PRetReplayInvariant016
open PRetShadowAppend014 PRetExecutionPrefixes018

variable {I : Instance}

theorem replayInvariant_frame {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (target next : State I)
    (hi : ReplayInvariant input C mode accounting source sample target)
    (hinfo : informationTrace next.history = informationTrace target.history)
    (hreviews : next.ledger.reviews = target.ledger.reviews)
    (hwritten : next.ledger.written = target.ledger.written)
    (hpairs : next.ledger.executions.map executionPair = target.ledger.executions.map executionPair) :
    ReplayInvariant input C mode accounting source sample next := by
  obtain ⟨packets, oldClock, hpackets, hreplay, hr, hw, hp⟩ := hi
  exact ⟨packets, oldClock, hinfo.trans hpackets, hreplay,
    hreviews.trans hr, hwritten.trans hw, hpairs ▸ hp⟩

/-- A genuine source response followed by the bounded public administrative
closure is a later genuine source prefix. No response is fabricated and
neither the policy's seed nor its observable input is enlarged. -/
theorem consume_actual {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (oldClock : ℕ) (packet : Packet I)
    (ha : (run input C mode accounting source sample oldClock).halted = false)
    (hselected : source sample.1 (run input C mode accounting source sample oldClock).history = packet.action)
    (hresponse : packet.applyPublic accounting (publicStartup (run input C mode accounting source sample oldClock)) =
      publicStartup (run input C mode accounting source sample (oldClock + 1))) :
    ∃ newClock, oldClock < newClock ∧
      consume accounting source sample.1 (publicStartup (run input C mode accounting source sample oldClock)) packet =
        some (publicStartup (run input C mode accounting source sample newClock)) := by
  let later := publicStartup (run input C mode accounting source sample (oldClock + 1))
  let settled := settle accounting source (I.stageCount + 2 * I.toolCount + 2) sample.1 later
  refine ⟨oldClock + 1 + settled.2, by omega, ?_⟩
  have hs := settle_actual input C mode accounting source hlegal sample
    (I.stageCount + 2 * I.toolCount + 2) (oldClock + 1)
  change settled.1 = publicStartup (run input C mode accounting source sample (oldClock + 1 + settled.2)) at hs
  rw [consume, ite_eq_left (show (publicStartup (run input C mode accounting source sample oldClock)).halted = false ∧
    source sample.1 (publicStartup (run input C mode accounting source sample oldClock)).history = packet.action from
      ⟨ha, hselected⟩), hresponse]
  exact congrArg some hs

theorem replayInvariant_packet {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (packets : List (Packet I)) (oldClock newClock : ℕ)
    (next : State I) (packet : Packet I)
    (hreplay : replay accounting source sample.1 packets =
      some (publicStartup (run input C mode accounting source sample oldClock)))
    (hconsume : consume accounting source sample.1 (publicStartup (run input C mode accounting source sample oldClock)) packet =
      some (publicStartup (run input C mode accounting source sample newClock)))
    (hinfo : informationTrace next.history = (packets ++ [packet]).flatMap Packet.events)
    (hreviews : next.ledger.reviews =
      (packet.applyPublic accounting (publicStartup (run input C mode accounting source sample oldClock))).reviews)
    (hwritten : next.ledger.written =
      (packet.applyPublic accounting (publicStartup (run input C mode accounting source sample oldClock))).written)
    (hpairs : (next.ledger.executions.map executionPair).IsPrefix
      ((run input C mode accounting source sample oldClock).ledger.executions.map executionPair)) :
    ReplayInvariant input C mode accounting source sample next := by
  have hframes :
      (publicStartup (run input C mode accounting source sample newClock)).reviews =
        (packet.applyPublic accounting (publicStartup (run input C mode accounting source sample oldClock))).reviews ∧
      (publicStartup (run input C mode accounting source sample newClock)).written =
        (packet.applyPublic accounting (publicStartup (run input C mode accounting source sample oldClock))).written := by
    unfold consume at hconsume
    split at hconsume
    · have heq := Option.some.inj hconsume
      have hf := settle_frames accounting source (I.stageCount + 2 * I.toolCount + 2) sample.1
        (packet.applyPublic accounting (publicStartup (run input C mode accounting source sample oldClock)))
      rw [heq] at hf
      exact ⟨hf.1, hf.2.1⟩
    · cases hconsume
  have hexec := consume_executions_prefix accounting source sample.1 _ _ packet hconsume
  have hp := hpairs.trans (hexec.map executionPair)
  refine ⟨packets ++ [packet], newClock, hinfo,
    replay_append_one accounting source sample.1 packets packet _ _ hreplay hconsume,
    hreviews.trans hframes.1.symm, hwritten.trans hframes.2.symm, hp⟩

end PaperProofs.Retained.PRetActualPacketReplay020
