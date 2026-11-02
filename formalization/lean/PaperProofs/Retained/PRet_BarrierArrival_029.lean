module

public import PaperProofs.Retained.PRet_FiniteSourceHalt_025
public import PaperProofs.Retained.PRet_PrebarrierProgress_028
public import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetBarrierArrival029

open Common Common.Native PRetDelayedPolicy010 PRetRunReplay023
open PRetPrebarrierProgress028 PRetFiniteSourceHalt025 PRetDelayedTerminalOnly011

variable {I : Instance}

theorem step_cursor_increase_frames (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {before next : State I} {action : Action I}
    (hs : Step input C mode accounting tapes before action next) (hlt : before.cursor < next.cursor) :
    next.halted = false ∧ next.ledger.commitments = before.ledger.commitments ∧
      next.ledger.executions = before.ledger.executions := by
  cases hs <;> simp_all [record, stopState, advanceLedger]

theorem prefix_prebarrier_active {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (hsuccess : runSuccess input C mode accounting source sample)
    {n : ℕ} {target : State I}
    (hp : Prefix input C .uncapped accounting (rule accounting source) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n target)
    (hbound : target.cursor < I.stageCount) : target.halted = false := by
  cases hp with
  | initial => rfl
  | @next n before target earlier step =>
    have hb : before.cursor < I.stageCount :=
      lt_of_le_of_lt (step_cursor_bounds input C .uncapped accounting _ step).1 hbound
    have hi := prefix_replayInvariant input C hearly mode accounting source hlegal sample earlier
    have ha := step_source_active input C .uncapped accounting _ step
    obtain ⟨nextRaw, hsRaw, haRaw⟩ := prebarrier_raw_step input C mode accounting source hlegal sample hsuccess earlier hi ha hb
    have hselected := PRetRetainedGuard007.guarded_action_of_step input C hearly accounting (raw accounting source)
      sample.1 _ _ earlier hsRaw
    change rule accounting source sample.1 before.history = raw accounting source sample.1 before.history at hselected
    rw [hselected] at step
    have heq := step_deterministic input C .uncapped accounting _ step hsRaw
    rw [heq]
    exact haRaw

theorem barrier_reached {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (hsuccess : runSuccess input C mode accounting source sample) :
    ∃ n, (run input C .uncapped accounting (rule accounting source) sample n).cursor = I.stageCount := by
  obtain ⟨last, hhalt, hgood⟩ := hsuccess
  let bound := (informationTrace (run input C mode accounting source sample last).history).length +
    I.stageCount + 2 * I.toolCount + 2
  have hh := delayed_halted_of_source_halted input C hretained mode accounting source hlegal sample last hhalt
  change (run input C .uncapped accounting (rule accounting source) sample bound).halted = true at hh
  have htarget := PRetRetainedGuard007.guarded_legal input C hretained accounting (raw accounting source)
  have hc := (run_cursorInvariant input C .uncapped accounting (rule accounting source) htarget sample bound).bound
  refine ⟨bound, ?_⟩
  by_contra hne
  have hlt : (run input C .uncapped accounting (rule accounting source) sample bound).cursor < I.stageCount := by omega
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (rule accounting source) htarget sample bound
  have ha := prefix_prebarrier_active input C hretained.1 mode accounting source hlegal sample ⟨last, hhalt, hgood⟩ hp hlt
  rw [hh] at ha
  cases ha

/-- The first actual barrier arrival has no allocation or execution. This
includes N=0 and uses the real delayed Policy, not an available-only policy
class or a hypothetical terminal ledger. -/
theorem clean_barrier_arrival {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (hsuccess : runSuccess input C mode accounting source sample) :
    ∃ n, (run input C .uncapped accounting (rule accounting source) sample n).cursor = I.stageCount ∧
      (run input C .uncapped accounting (rule accounting source) sample n).halted = false ∧
      (run input C .uncapped accounting (rule accounting source) sample n).ledger.commitments = [] ∧
      (run input C .uncapped accounting (rule accounting source) sample n).ledger.executions = [] := by
  classical
  have hex := barrier_reached input C hretained mode accounting source hlegal sample hsuccess
  obtain ⟨n, hn, hmin⟩ : ∃ n,
      (run input C .uncapped accounting (rule accounting source) sample n).cursor = I.stageCount ∧
      ∀ m < n, (run input C .uncapped accounting (rule accounting source) sample m).cursor ≠ I.stageCount :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ hm => Nat.find_min hex hm⟩
  cases n with
  | zero => exact ⟨0, hn, rfl, rfl, rfl⟩
  | succ n =>
    have htarget := PRetRetainedGuard007.guarded_legal input C hretained accounting (raw accounting source)
    have hc := (run_cursorInvariant input C .uncapped accounting (rule accounting source) htarget sample n).bound
    have hne := hmin n (Nat.lt_succ_self n)
    have hlt : (run input C .uncapped accounting (rule accounting source) sample n).cursor < I.stageCount := by omega
    obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (rule accounting source) htarget sample n
    have ha := prefix_prebarrier_active input C hretained.1 mode accounting source hlegal sample hsuccess hp hlt
    obtain ⟨next, hs⟩ := htarget sample.1 _ _ _ _ hp ha
    have hnext := run_succ_of_step input C .uncapped accounting (rule accounting source) sample n next ha hs
    have he := delayed_terminalOnly input C accounting source sample.1 _ _ _ _ hp hlt
    rw [hnext] at hn
    have hinc : (run input C .uncapped accounting (rule accounting source) sample n).cursor < next.cursor := by
      rw [hn]
      exact hlt
    have hf := step_cursor_increase_frames input C .uncapped accounting _ hs hinc
    refine ⟨n + 1, by rw [hnext]; exact hn, ?_, ?_, ?_⟩
    · rw [hnext]
      exact hf.1
    · rw [hnext]
      exact hf.2.1.trans he.1
    · rw [hnext]
      exact hf.2.2.trans he.2

end PaperProofs.Retained.PRetBarrierArrival029
