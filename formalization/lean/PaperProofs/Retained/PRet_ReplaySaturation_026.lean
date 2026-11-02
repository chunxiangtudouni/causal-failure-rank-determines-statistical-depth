module

public import PaperProofs.Retained.PRet_ReplayInvariant_016

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetReplaySaturation026

open Common Common.Native PRetInformationPackets006 PRetPublicAdministrativeReplay005

variable {I : Instance}

def SettleImage {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup : Startup I) : Prop :=
  ∃ base, startup = (settle accounting source (I.stageCount + 2 * I.toolCount + 2) seed base).1

theorem consume_settleImage {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup next : Startup I) (packet : Packet I)
    (hconsume : consume accounting source seed startup packet = some next) :
    SettleImage accounting source seed next := by
  unfold consume at hconsume
  split at hconsume
  · exact ⟨_, (Option.some.inj hconsume).symm⟩
  · cases hconsume

theorem fold_settleImage {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (packets : List (Packet I)) (startup next : Startup I)
    (himage : SettleImage accounting source seed startup)
    (hfold : packets.foldlM (consume accounting source seed) startup = some next) :
    SettleImage accounting source seed next := by
  induction packets generalizing startup with
  | nil =>
    have heq : startup = next := Option.some.inj hfold
    exact heq ▸ himage
  | cons packet later ih =>
    change (consume accounting source seed startup packet).bind
      (fun next => later.foldlM (consume accounting source seed) next) = some next at hfold
    obtain ⟨middle, hconsume, htail⟩ := Option.bind_eq_some_iff.mp hfold
    exact ih middle (consume_settleImage accounting source seed startup middle packet hconsume) htail

theorem replay_settleImage {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (packets : List (Packet I)) (next : Startup I)
    (hreplay : replay accounting source seed packets = some next) :
    SettleImage accounting source seed next :=
  fold_settleImage accounting source seed packets _ next ⟨_, rfl⟩ hreplay

theorem settleImage_stopped {Seed : Type*} (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (startup : Startup I) (himage : SettleImage accounting source seed startup)
    (hbound : position startup ≤ I.stageCount + 2 * I.toolCount + 1) :
    silentNext accounting startup (source seed startup.history) = none := by
  obtain ⟨base, hbase⟩ := himage
  have hposition := settle_position accounting source (I.stageCount + 2 * I.toolCount + 2) seed base
  rw [← hbase] at hposition
  have hcount : (settle accounting source (I.stageCount + 2 * I.toolCount + 2) seed base).2 <
      I.stageCount + 2 * I.toolCount + 2 := by omega
  have hs := settle_stops_of_count_lt accounting source (I.stageCount + 2 * I.toolCount + 2) seed base hcount
  rw [← hbase] at hs
  exact hs

/-- Every reachable original source cache in the replay has completed ALL
silent actions before exposing another genuine response. This is derived
from the real ledger bound, not asserted as a cache field or Policy premise. -/
theorem actual_replay_stopped {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (packets : List (Packet I)) (oldClock : ℕ)
    (hreplay : replay accounting source sample.1 packets =
      some (publicStartup (run input C mode accounting source sample oldClock))) :
    silentNext accounting (publicStartup (run input C mode accounting source sample oldClock))
      (source sample.1 (run input C mode accounting source sample oldClock).history) = none := by
  apply settleImage_stopped accounting source sample.1 _
    (replay_settleImage accounting source sample.1 packets _ hreplay)
  have hwf := run_ledgerWellFormed input C mode accounting source hlegal sample oldClock
  have hc : (run input C mode accounting source sample oldClock).ledger.commitments.length ≤ I.toolCount := by
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hwf.commitment_tools.length_le_card
  have he : (run input C mode accounting source sample oldClock).ledger.executions.length ≤ I.toolCount := by
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hwf.execution_tools.length_le_card
  exact position_le_bound _ hc he (run_cursorInvariant input C mode accounting source hlegal sample oldClock).bound

theorem stopped_active_information (accounting : NormalAccounting I) (startup : Startup I)
    (action : Action I) (ha : startup.halted = false)
    (hs : silentNext accounting startup action = none) :
    ∃ stage, action = .review stage ∨ ∃ bit, action = .write stage bit := by
  cases action with
  | review stage => exact ⟨stage, Or.inl rfl⟩
  | write stage bit => exact ⟨stage, Or.inr ⟨bit, rfl⟩⟩
  | allocate | execute | advance | stop | abandon =>
    simp only [silentNext, ha, Bool.false_eq_true, ↓reduceIte, silentAction, Option.some_ne_none] at hs

end PaperProofs.Retained.PRetReplaySaturation026
