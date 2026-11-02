module

public import PaperProofs.Retained.PRet_ReplaySaturation_026

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetSourceSuccess027

open Common Common.Native PRetInformationPackets006 PRetPublicAdministrativeReplay005
open PRetReplaySaturation026

variable {I : Instance}

theorem success_allWritten (C : Contract I) (ledger : Ledger I)
    (hwf : LedgerWellFormed ledger) (hs : ledger.success C) : allWritten ledger := by
  intro stage
  obtain hcorrect | ⟨execution, hmem, hstage⟩ := hs.2.2.2 stage
  · rw [hcorrect]
    exact Option.some_ne_none _
  · have hg := (hwf.genuine execution hmem).1
    rw [hstage] at hg
    rw [hg]
    exact Option.some_ne_none _

theorem halted_source_success {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (hsuccess : runSuccess input C mode accounting source sample)
    (oldClock : ℕ) (hhalt : (run input C mode accounting source sample oldClock).halted = true) :
    (run input C mode accounting source sample oldClock).ledger.success C := by
  obtain ⟨last, hlast, hs⟩ := hsuccess
  by_cases hle : oldClock ≤ last
  · have heq := run_after_halt input C mode accounting source sample oldClock hhalt (last - oldClock)
    rw [Nat.add_sub_of_le hle] at heq
    rw [heq] at hs
    exact hs
  · have hle' : last ≤ oldClock := by omega
    have heq := run_after_halt input C mode accounting source sample last hlast (oldClock - last)
    rw [Nat.add_sub_of_le hle'] at heq
    rw [heq]
    exact hs

theorem active_replay_information {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (packets : List (Packet I)) (oldClock : ℕ)
    (hreplay : replay accounting source sample.1 packets =
      some (publicStartup (run input C mode accounting source sample oldClock)))
    (ha : (run input C mode accounting source sample oldClock).halted = false) :
    ∃ stage, source sample.1 (run input C mode accounting source sample oldClock).history = .review stage ∨
      ∃ bit, source sample.1 (run input C mode accounting source sample oldClock).history = .write stage bit :=
  stopped_active_information accounting _ _ ha
    (actual_replay_stopped input C mode accounting source hlegal sample packets oldClock hreplay)

end PaperProofs.Retained.PRetSourceSuccess027
