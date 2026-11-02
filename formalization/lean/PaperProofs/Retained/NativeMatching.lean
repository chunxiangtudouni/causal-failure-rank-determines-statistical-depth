module

public import PaperProofs.Retained.Model
public import PaperProofs.Common.NativeDeadlines

set_option autoImplicit false
set_option warningAsError true

/-!
Pathwise native-to-matching facts. Every finite legal prefix, including a
failing or abandoned one, has a genuine matching of its executed stages.
On a successful ledger every ordinary mismatch is among those stages.
These statements neither select successful-path charges nor assert the full
random-history rearrangement bridge or a resource-qualified controller.
-/

@[expose] public section

namespace PaperProofs.Retained

open Common

variable {I : Instance}

def executedStages (L : Ledger I) : Finset I.Stage :=
  (L.executions.map (fun e => e.handle.stage)).toFinset

theorem mem_executedStages (L : Ledger I) (i : I.Stage) :
    i ∈ executedStages L ↔ ∃ e ∈ L.executions, e.handle.stage = i := by
  simp only [executedStages, List.mem_toFinset, List.mem_map]

def ordinaryMismatches (L : Ledger I) : Finset I.Stage :=
  Finset.univ.filter (fun i => L.written i = some (!L.truth i))

theorem mem_ordinaryMismatches (L : Ledger I) (i : I.Stage) :
    i ∈ ordinaryMismatches L ↔ L.written i = some (!L.truth i) := by
  simp only [ordinaryMismatches, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A witness uses only tools of actual execution records. Tool injectivity
comes from the proved ledger invariant, not from a supplied matching field. -/
theorem executedStages_matchable (L : Ledger I) (hwf : LedgerWellFormed L) :
    Matchable I (executedStages L) := by
  classical
  have hex (i : {i : I.Stage // i ∈ executedStages L}) :
      ∃ e ∈ L.executions, e.handle.stage = i.val := (mem_executedStages L i.val).mp i.property
  let chosen (i : {i : I.Stage // i ∈ executedStages L}) : Execution I := Classical.choose (hex i)
  have hmem (i : {i : I.Stage // i ∈ executedStages L}) : chosen i ∈ L.executions :=
    (Classical.choose_spec (hex i)).1
  have hstage (i : {i : I.Stage // i ∈ executedStages L}) : (chosen i).handle.stage = i.val :=
    (Classical.choose_spec (hex i)).2
  refine ⟨fun i => (chosen i).tool, ?_, ?_⟩
  · intro i j htool
    have heq : chosen i = chosen j :=
      List.inj_on_of_nodup_map hwf.execution_tools (hmem i) (hmem j) htool
    apply Subtype.ext
    rw [← hstage i, ← hstage j, heq]
  · intro i
    have hcompatible := hwf.compatible (chosen i) (hmem i)
    rwa [hstage i] at hcompatible

theorem executedStages_subset_mismatches (L : Ledger I) (hwf : LedgerWellFormed L) :
    executedStages L ⊆ ordinaryMismatches L := by
  intro i hi
  obtain ⟨e, he, hstage⟩ := (mem_executedStages L i).mp hi
  apply (mem_ordinaryMismatches L i).mpr
  simpa only [hstage] using (hwf.genuine e he).1

theorem mismatches_subset_executedStages_of_success (L : Ledger I) (C : Contract I)
    (hsuccess : L.success C) : ordinaryMismatches L ⊆ executedStages L := by
  intro i hi
  have hwrong := (mem_ordinaryMismatches L i).mp hi
  rcases hsuccess.2.2.2 i with hcorrect | hexecuted
  · rw [hwrong] at hcorrect
    cases htruth : L.truth i <;> simp only [htruth, Bool.not_false, Bool.not_true,
      Option.some.injEq, Bool.true_eq_false, Bool.false_eq_true] at hcorrect
  · exact (mem_executedStages L i).mpr hexecuted

theorem mismatches_matchable_of_success (L : Ledger I) (C : Contract I)
    (hwf : LedgerWellFormed L) (hsuccess : L.success C) : Matchable I (ordinaryMismatches L) :=
  (executedStages_matchable L hwf).subset (mismatches_subset_executedStages_of_success L C hsuccess)

theorem executedStages_eq_mismatches_of_success (L : Ledger I) (C : Contract I)
    (hwf : LedgerWellFormed L) (hsuccess : L.success C) :
    executedStages L = ordinaryMismatches L :=
  Finset.Subset.antisymm (executedStages_subset_mismatches L hwf)
    (mismatches_subset_executedStages_of_success L C hsuccess)

theorem prefix_executedStages_matchable (input : StatisticalInput I) (C : Contract I)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : Native.ReviewTapes input) {n : ℕ} {s : Native.State I}
    (hp : Native.Prefix input C mode accounting policy seed truth tapes n s) :
    Matchable I (executedStages s.ledger) :=
  executedStages_matchable s.ledger
    (Native.prefix_ledgerWellFormed input C mode accounting policy seed truth tapes hp)

theorem prefix_success_mismatches_matchable (input : StatisticalInput I) (C : Contract I)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : Native.ReviewTapes input) {n : ℕ} {s : Native.State I}
    (hp : Native.Prefix input C mode accounting policy seed truth tapes n s)
    (hsuccess : s.ledger.success C) : Matchable I (ordinaryMismatches s.ledger) :=
  (prefix_executedStages_matchable input C mode accounting policy seed truth tapes hp).subset
    (mismatches_subset_executedStages_of_success s.ledger C hsuccess)

theorem run_executedStages_matchable (input : StatisticalInput I) (C : Contract I)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (hlegal : Native.LegalRule input C mode accounting policy)
    (sample : Seed × input.World) (n : ℕ) :
    Matchable I (executedStages (Native.run input C mode accounting policy sample n).ledger) :=
  executedStages_matchable _
    (Native.run_ledgerWellFormed input C mode accounting policy hlegal sample n)

theorem run_success_mismatches_matchable (input : StatisticalInput I) (C : Contract I)
    (mode : Native.ResourceMode) (accounting : Native.NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (hlegal : Native.LegalRule input C mode accounting policy)
    (sample : Seed × input.World) (n : ℕ)
    (hsuccess : (Native.run input C mode accounting policy sample n).ledger.success C) :
    Matchable I (ordinaryMismatches (Native.run input C mode accounting policy sample n).ledger) :=
  (run_executedStages_matchable input C mode accounting policy hlegal sample n).subset
    (mismatches_subset_executedStages_of_success _ C hsuccess)

theorem mismatches_empty_of_success_no_tools (L : Ledger I) (C : Contract I)
    (hwf : LedgerWellFormed L) (hsuccess : L.success C) (hzero : I.toolCount = 0) :
    ordinaryMismatches L = ∅ := by
  have hcard := (mismatches_matchable_of_success L C hwf hsuccess).card_le_tools
  rw [hzero] at hcard
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)

/-- A real retained correction has an actual allocate Step followed by an
actual execute Step. The cap-relaxed mode removes only resource checks;
handles, compatibility, single use, commitment and execution all remain.
This is one correction pair, not yet a whole terminal matching algorithm. -/
theorem exists_uncapped_correction_pair (input : StatisticalInput I) (C : Contract I)
    (accounting : Native.NormalAccounting I) (tapes : Native.ReviewTapes input)
    (s : Native.State I) (h : MismatchHandle I) (r : I.Tool)
    (hactive : s.halted = false) (hwf : LedgerWellFormed s.ledger)
    (hhandle : Native.validHandle s h) (hcompatible : r ∈ I.eligible h.stage)
    (hallocation : C.allocation = .terminalBarrier) (hexecution : C.execution = .terminalBarrier)
    (htool : ∀ a ∈ s.ledger.commitments, a.tool ≠ r)
    (hstage : ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ h.stage) :
    ∃ committed repaired,
      Native.Step input C .uncapped accounting tapes s (.allocate h r) committed ∧
      Native.Step input C .uncapped accounting tapes committed (.execute h r) repaired ∧
      repaired.halted = false ∧
      (∀ handle, Native.validHandle repaired handle ↔ Native.validHandle s handle) ∧
      repaired.ledger.executions = s.ledger.executions ++ [⟨h, r, s.clock + 1⟩] ∧
      repaired.ledger.actualBill input.fees = s.ledger.actualBill input.fees +
        ENNReal.ofReal (input.fees.correction h.stage r : ℝ) := by
  let committed := Native.record accounting s (.allocate h r) [.committed h r]
    (Native.allocateLedger s h r) s.cursor false
  let repaired := Native.record accounting committed (.execute h r) [.executed h r]
    (Native.executeLedger committed h r) committed.cursor false
  have htoolExec : ∀ e ∈ s.ledger.executions, e.tool ≠ r := by
    intro e he heq
    obtain ⟨a, ha, _, hatool, _⟩ := hwf.backed e he
    exact htool a ha (hatool.trans heq)
  have hstageExec : ∀ e ∈ s.ledger.executions, e.handle.stage ≠ h.stage := by
    intro e he heq
    obtain ⟨a, ha, hahandle, _, _⟩ := hwf.backed e he
    apply hstage a ha
    rw [hahandle]
    exact heq
  have hallocStep : Native.Step input C .uncapped accounting tapes s (.allocate h r) committed := by
    apply Native.Step.allocate s h r hactive hhandle hcompatible htool hstage
    · simp [Native.allocationOpen, hallocation]
    · exact Or.inl rfl
  have hvalid : Native.validHandle committed h := hhandle
  have hbacked : ∃ a ∈ committed.ledger.commitments, a.handle = h ∧ a.tool = r := by
    exact ⟨⟨h, r, s.clock⟩, by simp [committed, Native.record, Native.allocateLedger], rfl, rfl⟩
  have hexecStep : Native.Step input C .uncapped accounting tapes committed (.execute h r) repaired := by
    apply Native.Step.execute committed h r rfl hvalid hcompatible hbacked htoolExec hstageExec
    · simp [Native.executionOpen, hexecution]
    · exact Or.inl rfl
  refine ⟨committed, repaired, hallocStep, hexecStep, rfl, fun _ => Iff.rfl, rfl, ?_⟩
  calc
    _ = (Native.executeLedger committed h r).actualBill input.fees := rfl
    _ = committed.ledger.actualBill input.fees + ENNReal.ofReal (input.fees.correction h.stage r : ℝ) :=
      Native.execute_actualBill committed h r input.fees
    _ = _ := rfl

end PaperProofs.Retained
