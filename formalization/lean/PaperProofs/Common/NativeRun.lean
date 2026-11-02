module

public import PaperProofs.Common.NativeExecution
public import PaperProofs.Common.NativeAccounting
public import PaperProofs.Common.NativeInvariant

/-!
The total probability-space interpreter follows real legal protocol prefixes.
The invalid-action completion is unreachable under LegalRule. All accounting
invariants, resource caps and charge monotonicity below are pathwise, without
conditioning on eventual task success or dropping failed-path charges.
-/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

theorem run_succ_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ)
    (h : (run input C mode accounting policy sample n).halted = true) :
    run input C mode accounting policy sample (n + 1) =
      run input C mode accounting policy sample n := by
  simp only [run, nextFromFrontier, h, ↓reduceIte]

theorem run_succ_of_step (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ) (s' : State I)
    (hactive : (run input C mode accounting policy sample n).halted = false)
    (hstep : Step input C mode accounting (worldTapes input sample.2)
      (run input C mode accounting policy sample n)
      (policy sample.1 (run input C mode accounting policy sample n).history) s') :
    run input C mode accounting policy sample (n + 1) = s' := by
  apply nextFromFrontier_eq_of_step input C mode accounting _ s' _ _ hactive
  exact (step_world_frontier_iff input C mode accounting sample.2 _ _ _).mp hstep

/-- Every interpreted state is an actual prefix state. After halt the same
state persists, so the prefix length can be smaller than the interpreter clock. -/
theorem run_has_prefix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World)
    (n : ℕ) : ∃ m ≤ n, Prefix input C mode accounting policy sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) m
      (run input C mode accounting policy sample n) := by
  induction n with
  | zero => exact ⟨0, le_rfl, .initial⟩
  | succ n ih =>
    obtain ⟨m, hmn, hp⟩ := ih
    by_cases hhalt : (run input C mode accounting policy sample n).halted = true
    · refine ⟨m, hmn.trans (Nat.le_succ n), ?_⟩
      rw [run_succ_of_halted input C mode accounting policy sample n hhalt]
      exact hp
    · have hactive : (run input C mode accounting policy sample n).halted = false :=
        Bool.eq_false_iff.mpr hhalt
      obtain ⟨s', hstep⟩ := hlegal sample.1 (input.truthAt sample.2)
        (worldTapes input sample.2) m _ hp hactive
      refine ⟨m + 1, Nat.succ_le_succ hmn, ?_⟩
      rw [run_succ_of_step input C mode accounting policy sample n s' hactive hstep]
      exact .next hp hstep

theorem run_ledgerWellFormed (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World)
    (n : ℕ) : LedgerWellFormed (run input C mode accounting policy sample n).ledger := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C mode accounting policy hlegal sample n
  exact prefix_ledgerWellFormed input C mode accounting policy sample.1 _ _ hp

theorem run_finiteCounters (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World)
    (n : ℕ) : FiniteCounters (run input C mode accounting policy sample n).ledger := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C mode accounting policy hlegal sample n
  exact prefix_finiteCounters input C mode accounting policy sample.1 _ _ hp

theorem run_native_obeysCaps (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) (sample : Seed × input.World)
    (n : ℕ) : (run input C .native accounting policy sample n).ledger.obeysCaps C := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .native accounting policy hlegal sample n
  exact prefix_native_obeysCaps input C accounting policy sample.1 _ _ hp

theorem run_actualCorrections_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World)
    (n : ℕ) : (run input C mode accounting policy sample n).ledger.executions.length ≤
      min I.stageCount I.toolCount :=
  Ledger.execution_count_le (run_ledgerWellFormed input C mode accounting policy hlegal sample n)

theorem nextFromFrontier_actualBill_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (s : State I)
    (action : Action I) (frontier : Frontier input) (F : Fees I) :
    s.ledger.actualBill F ≤
      (nextFromFrontier input C mode accounting s action frontier).ledger.actualBill F := by
  classical
  unfold nextFromFrontier
  split_ifs with hhalt hex
  · exact le_rfl
  · exact step_actualBill_mono input C mode accounting _ (Classical.choose_spec hex) F
  · simpa only [stop_actualBill] using (le_refl (s.ledger.actualBill F))

theorem run_bill_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) :
    Monotone (fun n ↦ (run input C mode accounting policy sample n).ledger.actualBill input.fees) := by
  apply monotone_nat_of_le_succ
  intro n
  exact nextFromFrontier_actualBill_mono input C mode accounting _ _ _ input.fees

/-- All charges through every prefix, including ones on a failing path, are
retained in the actual infinite-horizon bill. -/
theorem prefixBill_le_runActualBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ) :
    (run input C mode accounting policy sample n).ledger.actualBill input.fees ≤
      runActualBill input C mode accounting policy sample :=
  le_iSup (fun k : ℕ ↦ (run input C mode accounting policy sample k).ledger.actualBill input.fees) n

theorem run_after_halt (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hhalt : (run input C mode accounting policy sample n).halted = true) (extra : ℕ) :
    run input C mode accounting policy sample (n + extra) =
      run input C mode accounting policy sample n := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    rw [Nat.add_succ, run_succ_of_halted input C mode accounting policy sample (n + extra)]
    · exact ih
    · rw [ih]
      exact hhalt

/-- On a completed or abandoned finite run the supremum is exactly its full
ledger bill. The abandoned case is not assigned zero cost. -/
theorem runActualBill_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hhalt : (run input C mode accounting policy sample n).halted = true) :
    runActualBill input C mode accounting policy sample =
      (run input C mode accounting policy sample n).ledger.actualBill input.fees := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hkn : k ≤ n
    · exact run_bill_mono input C mode accounting policy sample hkn
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge hkn)
      rw [run_after_halt input C mode accounting policy sample n hhalt extra]
  · exact prefixBill_le_runActualBill input C mode accounting policy sample n

end PaperProofs.Common.Native
