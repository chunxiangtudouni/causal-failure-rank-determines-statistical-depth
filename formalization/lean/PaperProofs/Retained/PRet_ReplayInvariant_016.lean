module

public import PaperProofs.Retained.PRet_ExactTerminal_001
public import PaperProofs.Retained.PRet_ShadowInitial_012
public import PaperProofs.Retained.PRet_AdministrativeFrames_013

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetReplayInvariant016

open Common Common.Native PRetInformationPackets006 PRetPublicAdministrativeReplay005
open PRetExactTerminal001 PRetAdministrativeFrames013 PRetShadowInitial012

variable {I : Instance}

/-- An induction fact about ACTUAL source/target states, never a policy
field or a replacement for original R02. The source cache is identified
with a same-world real source run. No hidden truth is put in the cache. -/
def ReplayInvariant {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (target : State I) : Prop :=
  ∃ packets : List (Packet I), ∃ oldClock : ℕ,
    let original := run input C mode accounting source sample oldClock
    informationTrace target.history = packets.flatMap Packet.events ∧
    replay accounting source sample.1 packets = some (publicStartup original) ∧
    target.ledger.reviews = original.ledger.reviews ∧
    target.ledger.written = original.ledger.written ∧
    (target.ledger.executions.map executionPair).IsPrefix (original.ledger.executions.map executionPair)

theorem replayInvariant_initial {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) :
    ReplayInvariant input C mode accounting source sample (initial (input.truthAt sample.2)) := by
  obtain ⟨oldClock, _, hshadow⟩ := shadow_nil_actual input C mode accounting source hlegal sample
  have hreplay : replay accounting source sample.1 [] =
      some (publicStartup (run input C mode accounting source sample oldClock)) := hshadow
  let empty := publicStartup (initial (I := I) (fun _ => false))
  let result := settle accounting source (I.stageCount + 2 * I.toolCount + 2) sample.1 empty
  have hcache : result.1 = publicStartup (run input C mode accounting source sample oldClock) :=
    Option.some.inj hreplay
  have hf := settle_frames accounting source (I.stageCount + 2 * I.toolCount + 2) sample.1 empty
  change result.1.reviews = empty.reviews ∧ result.1.written = empty.written ∧
    result.1.writeSerial = empty.writeSerial ∧ result.1.reportTime = empty.reportTime at hf
  refine ⟨[], oldClock, rfl, hreplay, ?_, ?_, ?_⟩
  · have hreviews := (congrArg Startup.reviews hcache).symm.trans hf.1
    exact hreviews.symm
  · have hwritten := (congrArg Startup.written hcache).symm.trans hf.2.1
    exact hwritten.symm
  · exact List.nil_prefix

end PaperProofs.Retained.PRetReplayInvariant016
