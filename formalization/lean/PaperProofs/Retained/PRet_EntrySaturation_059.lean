module

public import PaperProofs.Retained.PRet_EntryRun_057
public import PaperProofs.Retained.PRet_ReplaySaturation_026

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntrySaturation059

open Common Common.Native PRetInformationPackets006 PRetPublicAdministrativeReplay005
open PRetEntryReplay045 PRetReplaySaturation026

variable {I : Instance}

theorem replayFrom_settleImage {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup : Startup I) (packets : List (Packet I)) (next : Startup I)
    (hreplay : replayFrom accounting source seed startup packets = some next) :
    SettleImage accounting source seed next :=
  fold_settleImage accounting source seed packets _ next ⟨startup, rfl⟩ hreplay

theorem actual_replayFrom_stopped {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (startup : Startup I) (packets : List (Packet I)) (oldClock : ℕ)
    (hreplay : replayFrom accounting source sample.1 startup packets =
      some (publicStartup (run input C mode accounting source sample oldClock))) :
    silentNext accounting (publicStartup (run input C mode accounting source sample oldClock))
      (source sample.1 (run input C mode accounting source sample oldClock).history) = none := by
  apply settleImage_stopped accounting source sample.1 _
    (replayFrom_settleImage accounting source sample.1 startup packets _ hreplay)
  have hwf := run_ledgerWellFormed input C mode accounting source hlegal sample oldClock
  have hc : (run input C mode accounting source sample oldClock).ledger.commitments.length ≤ I.toolCount := by
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hwf.commitment_tools.length_le_card
  have he : (run input C mode accounting source sample oldClock).ledger.executions.length ≤ I.toolCount := by
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hwf.execution_tools.length_le_card
  exact position_le_bound _ hc he (run_cursorInvariant input C mode accounting source hlegal sample oldClock).bound

theorem active_replayFrom_information {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (startup : Startup I) (packets : List (Packet I)) (oldClock : ℕ)
    (hreplay : replayFrom accounting source sample.1 startup packets =
      some (publicStartup (run input C mode accounting source sample oldClock)))
    (ha : (run input C mode accounting source sample oldClock).halted = false) :
    ∃ stage, source sample.1 (run input C mode accounting source sample oldClock).history = .review stage ∨
      ∃ bit, source sample.1 (run input C mode accounting source sample oldClock).history = .write stage bit :=
  stopped_active_information accounting (publicStartup (run input C mode accounting source sample oldClock))
    _ ha (actual_replayFrom_stopped input C mode accounting source hlegal sample startup packets oldClock hreplay)

end PaperProofs.Retained.PRetEntrySaturation059
