module

public import PaperProofs.Retained.PRet_ActualPacketReplay_020

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetInformationStep022

open Common Common.Native PRetPublicAdministrativeReplay005 PRetInformationPackets006
open PRetExactTerminal001 PRetReplayInvariant016 PRetShadowAppend014 PRetActualPacketReplay020

variable {I : Instance}

theorem review_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (target next : State I) (stage : I.Stage) (packets : List (Packet I)) (oldClock : ℕ)
    (hpackets : informationTrace target.history = packets.flatMap Packet.events)
    (hreplay : replay accounting source sample.1 packets =
      some (publicStartup (run input C mode accounting source sample oldClock)))
    (hreviews : target.ledger.reviews = (run input C mode accounting source sample oldClock).ledger.reviews)
    (hwritten : target.ledger.written = (run input C mode accounting source sample oldClock).ledger.written)
    (hpairs : (target.ledger.executions.map executionPair).IsPrefix
      ((run input C mode accounting source sample oldClock).ledger.executions.map executionPair))
    (ha : (run input C mode accounting source sample oldClock).halted = false)
    (hselected : source sample.1 (run input C mode accounting source sample oldClock).history = .review stage)
    (hstep : Step input C .uncapped accounting (worldTapes input sample.2) target (.review stage) next) :
    ReplayInvariant input C mode accounting source sample next := by
  let original := run input C mode accounting source sample oldClock
  let packet := Packet.review stage ((worldTapes input sample.2) stage (original.ledger.reviews stage).toNat).val
  obtain ⟨prefixClock, _, hprefix⟩ := run_has_prefix input C mode accounting source hlegal sample oldClock
  obtain ⟨sourceNext, hsourceStep⟩ := hlegal sample.1 _ _ prefixClock _ hprefix ha
  have hnext := run_succ_of_step input C mode accounting source sample oldClock sourceNext ha hsourceStep
  rw [hselected] at hsourceStep
  have hresponse : packet.applyPublic accounting (publicStartup original) =
      publicStartup (run input C mode accounting source sample (oldClock + 1)) := by
    rw [hnext]
    cases hsourceStep
    exact (publicStartup_review accounting original stage _).symm
  obtain ⟨newClock, _, hconsume⟩ := consume_actual input C mode accounting source hlegal sample oldClock packet ha hselected hresponse
  apply replayInvariant_packet input C mode accounting source sample packets oldClock newClock next packet hreplay hconsume
  · cases hstep
    change informationTrace (target.history ++ [.observation stage
      ((worldTapes input sample.2) stage (target.ledger.reviews stage).toNat).val]) = _
    rw [informationTrace_append, hpackets]
    change packets.flatMap Packet.events ++ [.observation stage
      ((worldTapes input sample.2) stage (target.ledger.reviews stage).toNat).val] = _
    dsimp only [packet, original]
    rw [List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Packet.events]
    rw [hreviews]
  · cases hstep
    change Function.update target.ledger.reviews stage (target.ledger.reviews stage + 1) =
      Function.update original.ledger.reviews stage (original.ledger.reviews stage + 1)
    rw [hreviews]
  · cases hstep
    exact hwritten
  · cases hstep
    exact hpairs

theorem write_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (target next : State I) (stage : I.Stage) (bit : Bool)
    (packets : List (Packet I)) (oldClock : ℕ)
    (hpackets : informationTrace target.history = packets.flatMap Packet.events)
    (hreplay : replay accounting source sample.1 packets =
      some (publicStartup (run input C mode accounting source sample oldClock)))
    (hreviews : target.ledger.reviews = (run input C mode accounting source sample oldClock).ledger.reviews)
    (hwritten : target.ledger.written = (run input C mode accounting source sample oldClock).ledger.written)
    (htruth : target.ledger.truth = (run input C mode accounting source sample oldClock).ledger.truth)
    (hpairs : (target.ledger.executions.map executionPair).IsPrefix
      ((run input C mode accounting source sample oldClock).ledger.executions.map executionPair))
    (ha : (run input C mode accounting source sample oldClock).halted = false)
    (hselected : source sample.1 (run input C mode accounting source sample oldClock).history = .write stage bit)
    (hstep : Step input C .uncapped accounting (worldTapes input sample.2) target (.write stage bit) next) :
    ReplayInvariant input C mode accounting source sample next := by
  let original := run input C mode accounting source sample oldClock
  let packet := Packet.write stage bit (original.ledger.truth stage)
  obtain ⟨prefixClock, _, hprefix⟩ := run_has_prefix input C mode accounting source hlegal sample oldClock
  obtain ⟨sourceNext, hsourceStep⟩ := hlegal sample.1 _ _ prefixClock _ hprefix ha
  have hnext := run_succ_of_step input C mode accounting source sample oldClock sourceNext ha hsourceStep
  rw [hselected] at hsourceStep
  have hresponse : packet.applyPublic accounting (publicStartup original) =
      publicStartup (run input C mode accounting source sample (oldClock + 1)) := by
    rw [hnext]
    cases hsourceStep
    exact (publicStartup_write_early C hearly accounting original stage bit).symm
  obtain ⟨newClock, _, hconsume⟩ := consume_actual input C mode accounting source hlegal sample oldClock packet ha hselected hresponse
  apply replayInvariant_packet input C mode accounting source sample packets oldClock newClock next packet hreplay hconsume
  · cases hstep
    change informationTrace (target.history ++ writeResponses C target stage bit) = _
    rw [informationTrace_append, hpackets]
    dsimp only [packet, original]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, writeResponses, hearly, ↓reduceIte, informationTrace,
      informationEvent, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      Packet.events, writeLedger]
    rw [htruth]
    rfl
  · cases hstep
    simpa only [record, reportedWriteLedger, hearly, ↓reduceIte, writeLedger,
      Packet.applyPublic, Startup.writePublic, publicStartup] using hreviews
  · cases hstep
    simp only [record, reportedWriteLedger, hearly, ↓reduceIte, writeLedger,
      Packet.applyPublic, Startup.writePublic, publicStartup]
    rw [hwritten]
  · cases hstep
    simpa only [record, reportedWriteLedger, hearly, ↓reduceIte, writeLedger] using hpairs

end PaperProofs.Retained.PRetInformationStep022
