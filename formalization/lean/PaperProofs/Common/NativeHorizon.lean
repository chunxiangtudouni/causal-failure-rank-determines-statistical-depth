module

public import PaperProofs.Common.NativeHistoryReplay
public import PaperProofs.Common.NativeCausality
import Lean.Elab.Tactic.Omega

/-!
A uniform finite bound for the returned-action native interpreter. This is
derived from finite original quotas and one-use/write/advance permissions.
It does not impose termination on uncapped comparisons or change the separate
partial-policy representation of a finite-paid call that never returns.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

def writtenPorts (L : Ledger I) : Finset I.Stage :=
  Finset.univ.filter (fun stage => L.written stage ≠ none)

noncomputable def actionProgress (s : State I) : ℕ∞ :=
  (∑ stage, s.ledger.reviews stage) + s.ledger.commitments.length +
    s.ledger.executions.length + s.cursor + (writtenPorts s.ledger).card +
      if s.halted then 1 else 0

private theorem actionProgress_record (accounting : NormalAccounting I) (s : State I) (action : Action I)
    (responses : List (VisibleEvent I)) (L : Ledger I) (cursor : ℕ) (halted : Bool) :
    actionProgress (record accounting s action responses L cursor halted) =
      (∑ stage, L.reviews stage) + L.commitments.length + L.executions.length + cursor +
        (writtenPorts L).card + if halted then 1 else 0 := rfl

private theorem writtenPorts_review (s : State I) (stage : I.Stage) :
    writtenPorts (reviewLedger s stage) = writtenPorts s.ledger := rfl

private theorem writtenPorts_allocate (s : State I) (handle : MismatchHandle I) (tool : I.Tool) :
    writtenPorts (allocateLedger s handle tool) = writtenPorts s.ledger := rfl

private theorem writtenPorts_execute (s : State I) (handle : MismatchHandle I) (tool : I.Tool) :
    writtenPorts (executeLedger s handle tool) = writtenPorts s.ledger := rfl

private theorem writtenPorts_write (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    writtenPorts (reportedWriteLedger C s stage bit) = insert stage (writtenPorts s.ledger) := by
  classical
  have hw : (reportedWriteLedger C s stage bit).written =
      Function.update s.ledger.written stage (some bit) := by
    simp only [reportedWriteLedger]
    split_ifs <;> rfl
  ext other
  by_cases heq : other = stage
  · subst other
    simp [writtenPorts, hw]
  · simp [writtenPorts, hw, heq]

private theorem writtenPorts_write_card (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool)
    (hopen : s.ledger.written stage = none) :
    (writtenPorts (reportedWriteLedger C s stage bit)).card = (writtenPorts s.ledger).card + 1 := by
  rw [writtenPorts_write, Finset.card_insert_of_notMem]
  simp [writtenPorts, hopen]

private theorem reportedWrite_progress (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool)
    (hopen : s.ledger.written stage = none) :
    (∑ i, (reportedWriteLedger C s stage bit).reviews i) +
        (reportedWriteLedger C s stage bit).commitments.length +
        (reportedWriteLedger C s stage bit).executions.length + s.cursor +
        (writtenPorts (reportedWriteLedger C s stage bit)).card =
      (∑ i, s.ledger.reviews i) + s.ledger.commitments.length +
        s.ledger.executions.length + s.cursor + (writtenPorts s.ledger).card + (1 : ℕ∞) := by
  rw [writtenPorts_write_card C s stage bit hopen]
  have hf : (reportedWriteLedger C s stage bit).reviews = s.ledger.reviews ∧
      (reportedWriteLedger C s stage bit).commitments = s.ledger.commitments ∧
      (reportedWriteLedger C s stage bit).executions = s.ledger.executions := by
    simp only [reportedWriteLedger]
    split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  simp only [hf.1, hf.2.1, hf.2.2, Nat.cast_add, Nat.cast_one, add_assoc]

theorem step_actionProgress (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I}
    (step : Step input C mode accounting tapes s action next) :
    actionProgress next = actionProgress s + 1 := by
  cases step with
  | review stage live port resources =>
    have ha := live.1
    have hsum : (∑ i, (reviewLedger s stage).reviews i) = (∑ i, s.ledger.reviews i) + 1 := by
      simp only [reviewLedger]
      rw [Finset.sum_update_of_mem (Finset.mem_univ stage)]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ stage)]
      simp only [Finset.sdiff_singleton_eq_erase]
      ac_rfl
    rw [actionProgress_record, writtenPorts_review, hsum]
    simp only [actionProgress, reviewLedger, ha, Bool.false_eq_true, ↓reduceIte, add_zero]
    ac_rfl
  | write stage bit live port resources =>
    have hp := reportedWrite_progress C s stage bit port
    rw [actionProgress_record]
    simpa only [actionProgress, live.1, Bool.false_eq_true, ↓reduceIte, add_zero] using hp
  | allocate handle tool active valid compatible unused unallocated window resources =>
    rw [actionProgress_record, writtenPorts_allocate]
    simp only [actionProgress, allocateLedger, active, Bool.false_eq_true,
      ↓reduceIte, List.length_append, List.length_singleton, ENat.natCast_add, ENat.natCast_one, add_zero]
    ac_rfl
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    rw [actionProgress_record, writtenPorts_execute]
    simp only [actionProgress, executeLedger, active, Bool.false_eq_true,
      ↓reduceIte, List.length_append, List.length_singleton, ENat.natCast_add, ENat.natCast_one, add_zero]
    ac_rfl
  | advance stage live written resources =>
    simp only [actionProgress, record, advanceLedger, writtenPorts, live.1, Bool.false_eq_true,
      ↓reduceIte, Nat.cast_add, Nat.cast_one, add_zero]
    ac_rfl
  | stop active | abandon active =>
    simp only [actionProgress, stopState, writtenPorts, active, Bool.false_eq_true,
      ↓reduceIte, add_zero]

theorem prefix_actionProgress (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s) : actionProgress s = n := by
  induction hp with
  | initial => simp [actionProgress, initial, writtenPorts]
  | next earlier step ih => rw [step_actionProgress input C mode accounting tapes step, ih, Nat.cast_add, Nat.cast_one]

def nativeActionBound (C : Contract I) : ℕ :=
  (∑ stage, C.reviewQuota stage) + I.toolCount + I.toolCount + I.stageCount + I.stageCount + 1

private theorem enat_natCast_sum {α : Type*} (items : Finset α) (f : α → ℕ) :
    ((∑ item ∈ items, f item : ℕ) : ℕ∞) = ∑ item ∈ items, (f item : ℕ∞) := by
  classical
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item items hnot ih =>
    simp only [Finset.sum_insert hnot, ENat.natCast_add, ih]

/-- The progress potential is bounded by the original finite quotas and
the protocol's one-use tool, write-port, and cursor invariants. -/
theorem prefix_native_actionProgress_le (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .native accounting policy seed truth tapes n s) :
    actionProgress s ≤ (nativeActionBound C : ℕ∞) := by
  have hcaps := prefix_native_obeysCaps input C accounting policy seed truth tapes hp
  have hwf := prefix_ledgerWellFormed input C .native accounting policy seed truth tapes hp
  have hcursor := (prefix_cursorInvariant input C .native accounting policy seed truth tapes hp).bound
  have hreviews : (∑ stage, s.ledger.reviews stage) ≤ ((∑ stage, C.reviewQuota stage : ℕ) : ℕ∞) := by
    rw [enat_natCast_sum]
    exact Finset.sum_le_sum (fun stage _ => hcaps.1 stage)
  have hcommitments : s.ledger.commitments.length ≤ I.toolCount := by
    have hh := hwf.commitment_tools.length_le_card
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hh
  have hexecutions : s.ledger.executions.length ≤ I.toolCount :=
    (Ledger.execution_count_le hwf).trans (min_le_right _ _)
  have hwritten : (writtenPorts s.ledger).card ≤ I.stageCount := by
    have hh := Finset.card_le_card (Finset.filter_subset (fun stage : I.Stage => s.ledger.written stage ≠ none) Finset.univ)
    simpa only [writtenPorts, Finset.card_univ, Instance.Stage, Instance.stageCount, Fintype.card_fin] using hh
  have hhalted : (if s.halted then (1 : ℕ∞) else 0) ≤ 1 := by
    cases s.halted <;> simp
  have ht := add_le_add
    (add_le_add
      (add_le_add
        (add_le_add (add_le_add hreviews (ENat.natCast_le_natCast.mpr hcommitments))
          (ENat.natCast_le_natCast.mpr hexecutions))
        (ENat.natCast_le_natCast.mpr hcursor))
      (ENat.natCast_le_natCast.mpr hwritten)) hhalted
  simpa only [actionProgress, nativeActionBound, ENat.natCast_add, ENat.natCast_one] using ht

/-- Every actual native Prefix has uniformly bounded returned-action length. -/
theorem prefix_native_length_le (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .native accounting policy seed truth tapes n s) :
    n ≤ nativeActionBound C := by
  have hh := prefix_native_actionProgress_le input C accounting policy seed truth tapes hp
  rw [prefix_actionProgress input C .native accounting policy seed truth tapes hp] at hh
  exact ENat.natCast_le_natCast.mp hh

theorem step_clock (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (step : Step input C mode accounting tapes s action next) :
    next.clock = s.clock + 1 := by
  cases step <;> rfl

theorem prefix_clock (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) : s.clock = n := by
  induction hp with
  | initial => rfl
  | next _ step ih => rw [step_clock input C mode accounting tapes step, ih]

/-- Before halt, the interpreter has performed exactly its clock index in
returned actions. A halted interpreter never resumes an active Prefix. -/
theorem run_prefix_of_active {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World) (n : ℕ)
    (hactive : (run input C mode accounting policy sample n).halted = false) :
    Prefix input C mode accounting policy sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n
      (run input C mode accounting policy sample n) := by
  induction n with
  | zero => exact .initial
  | succ n ih =>
    by_cases hh : (run input C mode accounting policy sample n).halted = true
    · rw [run_succ_of_halted input C mode accounting policy sample n hh, hh] at hactive
      cases hactive
    · have ha : (run input C mode accounting policy sample n).halted = false := Bool.eq_false_iff.mpr hh
      have hp := ih ha
      obtain ⟨next, hs⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n _ hp ha
      rw [run_succ_of_step input C mode accounting policy sample n next ha hs]
      exact .next hp hs

theorem run_clock_eq_index_of_active {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World) (n : ℕ)
    (hactive : (run input C mode accounting policy sample n).halted = false) :
    (run input C mode accounting policy sample n).clock = n :=
  prefix_clock input C mode accounting policy sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
    (run_prefix_of_active input C mode accounting policy hlegal sample n hactive)

/-- Any legal returned-action native rule has halted by the uniform action
horizon, on every sample and for an arbitrary seed universe. This says
nothing about the host computation returning a next action. -/
theorem run_halted_nativeActionBound_succ {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) (sample : Seed × input.World) :
    (run input C .native accounting policy sample (nativeActionBound C + 1)).halted = true := by
  by_contra hh
  have ha : (run input C .native accounting policy sample (nativeActionBound C + 1)).halted = false := Bool.eq_false_iff.mpr hh
  have hp := run_prefix_of_active input C .native accounting policy hlegal sample (nativeActionBound C + 1) ha
  have hn := prefix_native_length_le input C accounting policy sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  omega

theorem run_halted_of_nativeActionBound_lt {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C .native accounting policy) (sample : Seed × input.World)
    (n : ℕ) (hn : nativeActionBound C < n) : (run input C .native accounting policy sample n).halted = true := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hn)
  have hh := run_halted_nativeActionBound_succ input C accounting policy hlegal sample
  rw [run_after_halt input C .native accounting policy sample (nativeActionBound C + 1) hh extra]
  exact hh

end PaperProofs.Common.Native
