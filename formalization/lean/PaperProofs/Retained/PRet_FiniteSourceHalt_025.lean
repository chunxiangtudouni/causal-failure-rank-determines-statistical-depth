module

public import PaperProofs.Retained.PRet_PathwiseDomination_024
public import PaperProofs.Retained.PRet_AdministrativeClock_003
public import PaperProofs.Common.NativeHorizon
public import PaperProofs.Common.NativePreReportCausality

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFiniteSourceHalt025

open Common Common.Native PRetAdministrativeClock003 PRetShadowAppend014
open PRetDelayedPolicy010 PRetRunReplay023 PRetReplayConsequences017

variable {I : Instance}

theorem run_history_prefix_add {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) (n extra : ℕ) :
    (run input C mode accounting source sample n).history.IsPrefix
      (run input C mode accounting source sample (n + extra)).history := by
  induction extra with
  | zero => exact List.prefix_rfl
  | succ extra ih =>
    by_cases hh : (run input C mode accounting source sample (n + extra)).halted = true
    · rw [Nat.add_succ, run_succ_of_halted input C mode accounting source sample (n + extra) hh]
      exact ih
    · have ha := Bool.eq_false_iff.mpr hh
      obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting source hlegal sample (n + extra)
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      rw [Nat.add_succ, run_succ_of_step input C mode accounting source sample (n + extra) next ha hs]
      obtain ⟨suffix, hsuffix⟩ := step_history_extends input C mode accounting _ hs
      exact ih.trans ⟨suffix, hsuffix.symm⟩

theorem informationTrace_prefix (first later : List (VisibleEvent I)) (hp : first.IsPrefix later) :
    (informationTrace first).IsPrefix (informationTrace later) := by
  obtain ⟨suffix, rfl⟩ := hp
  exact ⟨informationTrace suffix, (informationTrace_append first suffix).symm⟩

theorem source_information_prefix_of_halted {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) (last n : ℕ)
    (hhalt : (run input C mode accounting source sample last).halted = true) :
    (informationTrace (run input C mode accounting source sample n).history).IsPrefix
      (informationTrace (run input C mode accounting source sample last).history) := by
  by_cases hn : n ≤ last
  · have hp := run_history_prefix_add input C mode accounting source hlegal sample n (last - n)
    rw [Nat.add_sub_of_le hn] at hp
    exact informationTrace_prefix _ _ hp
  · have hlast : last ≤ n := by omega
    have heq := run_after_halt input C mode accounting source sample last hhalt (n - last)
    rw [Nat.add_sub_of_le hlast] at heq
    rw [heq]

/-- A halted source bounds every delayed information prefix, including
target failure prefixes. No success, pending-payment or controller progress
assumption is hidden in this finite information bound. -/
theorem delayed_information_bound {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (last : ℕ)
    (hhalt : (run input C mode accounting source sample last).halted = true) (n : ℕ) :
    (informationTrace (run input C .uncapped accounting (rule accounting source) sample n).history).length ≤
      (informationTrace (run input C mode accounting source sample last).history).length := by
  obtain ⟨oldClock, hshadow, hinfo⟩ := PRetPathwiseDomination024.shadow_run input C hretained mode accounting source hlegal sample n
  rw [hshadow] at hinfo
  rw [← hinfo]
  exact (source_information_prefix_of_halted input C mode accounting source hlegal sample last oldClock hhalt).length_le

/-- The existing administrative clock bound supplies finite delayed halt.
This theorem does NOT assert that the halt is successful; that separate
obligation must exclude terminal payment rejection and source-failure stops. -/
theorem delayed_halted_of_source_halted {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (last : ℕ)
    (hhalt : (run input C mode accounting source sample last).halted = true) :
    (run input C .uncapped accounting (rule accounting source) sample
      ((informationTrace (run input C mode accounting source sample last).history).length +
        I.stageCount + 2 * I.toolCount + 2)).halted = true := by
  let bound := (informationTrace (run input C mode accounting source sample last).history).length +
    I.stageCount + 2 * I.toolCount + 2
  by_contra hh
  have ha : (run input C .uncapped accounting (rule accounting source) sample bound).halted = false :=
    Bool.eq_false_iff.mpr hh
  have htarget := PRetRetainedGuard007.guarded_legal input C hretained accounting (raw accounting source)
  have hp := run_prefix_of_active input C .uncapped accounting (rule accounting source) htarget sample bound ha
  have hc := prefix_clock_le_information input C hretained.1 .uncapped accounting (rule accounting source) sample.1 _ _ hp
  have hi := delayed_information_bound input C hretained mode accounting source hlegal sample last hhalt bound
  dsimp only [bound] at hc hi
  omega

end PaperProofs.Retained.PRetFiniteSourceHalt025
