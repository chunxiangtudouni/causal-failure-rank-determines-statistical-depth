module

public import PaperProofs.Retained.PRet_EntryReplay_045
public import PaperProofs.Retained.PRet_AdministrativeFrames_013
public import PaperProofs.Common.HistorySuffixRun

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryInvariant050

open Common Common.Native PRetPublicAdministrativeReplay005 PRetInformationPackets006
open PRetEntryReplay045 PRetAdministrativeFrames013

variable {I : Instance}

/-- An actual-state induction fact, NOT a policy field/admissibility premise.
Only future reviews and ordinary writes are compared; original source paid
actions remain in its real public shadow and are not added to the fresh run. -/
def EntryInvariant {Seed : Type*} (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed) (sample : Seed × input.World)
    (first start : ℕ) (startup : Startup I) (target : State (I.freshSuffix first)) : Prop :=
  ∃ packets : List (Packet (I.freshSuffix first)), ∃ oldClock : ℕ, start ≤ oldClock ∧
    informationTrace target.history = packets.flatMap Packet.events ∧
    replayFrom accounting source sample.1 startup (packets.map (liftPacket first)) =
      some (publicStartup (run input C mode accounting source sample oldClock)) ∧
    target.ledger.reviews = (fun stage => (run input C mode accounting source sample oldClock).ledger.reviews (I.freshStageLift first stage)) ∧
    target.ledger.written = (fun stage => (run input C mode accounting source sample oldClock).ledger.written (I.freshStageLift first stage))

theorem entryInvariant_initial {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample) :
    EntryInvariant input C mode accounting source sample first start
      (publicStartup (run input C mode accounting source sample start))
      (initial ((input.freshSuffix first).truthAt (input.restrictFreshWorld first sample.2))) := by
  let startup := publicStartup (run input C mode accounting source sample start)
  let result := settle accounting source (I.stageCount + 2 * I.toolCount + 2) sample.1 startup
  have hcache : result.1 = publicStartup (run input C mode accounting source sample (start + result.2)) :=
    settle_actual input C mode accounting source hlegal sample (I.stageCount + 2 * I.toolCount + 2) start
  have hf := settle_frames accounting source (I.stageCount + 2 * I.toolCount + 2) sample.1 startup
  change result.1.reviews = startup.reviews ∧ result.1.written = startup.written ∧
    result.1.writeSerial = startup.writeSerial ∧ result.1.reportTime = startup.reportTime at hf
  have hreviews : (run input C mode accounting source sample (start + result.2)).ledger.reviews =
      (run input C mode accounting source sample start).ledger.reviews :=
    (congrArg Startup.reviews hcache).symm.trans hf.1
  have hwritten : (run input C mode accounting source sample (start + result.2)).ledger.written =
      (run input C mode accounting source sample start).ledger.written :=
    (congrArg Startup.written hcache).symm.trans hf.2.1
  have hunborn := (firstEntryAt_unborn input C mode accounting source hlegal sample first start hentry).2
  refine ⟨[], start + result.2, Nat.le_add_right _ _, rfl, ?_, ?_, ?_⟩
  · exact congrArg some hcache
  · funext stage
    change 0 = (run input C mode accounting source sample (start + result.2)).ledger.reviews (I.freshStageLift first stage)
    rw [hreviews]
    exact (hunborn _ (by change first ≤ first + stage.val; omega)).2.symm
  · funext stage
    change none = (run input C mode accounting source sample (start + result.2)).ledger.written (I.freshStageLift first stage)
    rw [hwritten]
    exact (hunborn _ (by change first ≤ first + stage.val; omega)).1.symm

theorem shadowFrom_of_entryInvariant {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (first start : ℕ) (startup : Startup I) (target : State (I.freshSuffix first))
    (hi : EntryInvariant input C mode accounting source sample first start startup target) :
    ∃ oldClock ≥ start,
      shadowFrom first accounting source startup sample.1 target.history =
        some (publicStartup (run input C mode accounting source sample oldClock)) := by
  obtain ⟨packets, oldClock, hclock, hinfo, hreplay, _, _⟩ := hi
  refine ⟨oldClock, hclock, ?_⟩
  unfold shadowFrom
  rw [hinfo, parse_packets]
  exact hreplay

theorem source_cursor_ge_entry {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) (first start oldClock : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample) (hclock : start ≤ oldClock) :
    first ≤ (run input C mode accounting source sample oldClock).cursor := by
  have hc := run_cursor_monotone input C mode accounting source hlegal sample hclock
  change (run input C mode accounting source sample start).cursor ≤
    (run input C mode accounting source sample oldClock).cursor at hc
  rw [hentry.1] at hc
  exact hc

end PaperProofs.Retained.PRetEntryInvariant050
