module

public import PaperProofs.Retained.Controller

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetOutputCompletion049

open Common Common.Native

variable {I : Instance}

/-- Native finished=true records actual ordinary completion. This fact is
weaker than native success and applies to the ORIGINAL retained freshSuccess
predicate even when a source has not executed any terminal repairs. -/
theorem prefix_finished_allWritten {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting source seed truth tapes n s) :
    s.ledger.finished = true → allWritten s.ledger := by
  classical
  induction hp with
  | initial => intro hf; cases hf
  | @next n s s' earlier step ih =>
    generalize haction : source seed s.history = action at step
    cases step with
    | write stage bit live port resources =>
      intro hf
      have hfinished : s.ledger.finished = true := by
        change (reportedWriteLedger C s stage bit).finished = true at hf
        simp only [reportedWriteLedger] at hf
        split_ifs at hf <;> exact hf
      have hall := ih hfinished
      have hw : (reportedWriteLedger C s stage bit).written = Function.update s.ledger.written stage (some bit) := by
        classical
        simp only [reportedWriteLedger]
        split_ifs <;> rfl
      intro current
      change (reportedWriteLedger C s stage bit).written current ≠ none
      rw [hw]
      by_cases heq : current = stage
      · subst current
        simp
      · rw [Function.update_of_ne heq]
        exact hall current
    | stop | abandon =>
      intro hf
      change decide (allWritten s.ledger) = true at hf
      exact of_decide_eq_true hf
    | review | allocate | execute | advance => exact ih

theorem run_finished_allWritten {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) (n : ℕ)
    (hf : (run input C mode accounting source sample n).ledger.finished = true) :
    allWritten (run input C mode accounting source sample n).ledger := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C mode accounting source hlegal sample n
  exact prefix_finished_allWritten input C mode accounting source sample.1 _ _ hp hf

/-- The runtime liveness input does NOT assume native success. This is the
same actual terminal completion supplied by both native runSuccess and the
original freshSuccess; matching is handled by a later independent lemma. -/
theorem halted_completed_prefix {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (hcomplete : ∃ last, (run input C mode accounting source sample last).halted = true ∧
      (run input C mode accounting source sample last).ledger.finished = true ∧
      (run input C mode accounting source sample last).ledger.abandoned = false)
    (oldClock : ℕ) (hh : (run input C mode accounting source sample oldClock).halted = true) :
    (run input C mode accounting source sample oldClock).ledger.finished = true ∧
      (run input C mode accounting source sample oldClock).ledger.abandoned = false ∧
      allWritten (run input C mode accounting source sample oldClock).ledger := by
  obtain ⟨last, hlast, hf, ha⟩ := hcomplete
  have hsame : run input C mode accounting source sample oldClock = run input C mode accounting source sample last := by
    by_cases hle : oldClock ≤ last
    · have heq := run_after_halt input C mode accounting source sample oldClock hh (last - oldClock)
      rw [Nat.add_sub_of_le hle] at heq
      exact heq.symm
    · have hle' : last ≤ oldClock := by omega
      have heq := run_after_halt input C mode accounting source sample last hlast (oldClock - last)
      rw [Nat.add_sub_of_le hle'] at heq
      exact heq
  rw [hsame]
  exact ⟨hf, ha, run_finished_allWritten input C mode accounting source hlegal sample last hf⟩

theorem nativeSuccess_completed {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (hs : runSuccess input C mode accounting source sample) :
    ∃ last, (run input C mode accounting source sample last).halted = true ∧
      (run input C mode accounting source sample last).ledger.finished = true ∧
      (run input C mode accounting source sample last).ledger.abandoned = false := by
  obtain ⟨last, hh, hs⟩ := hs
  exact ⟨last, hh, hs.1, hs.2.1⟩

end PaperProofs.Retained.PRetOutputCompletion049
