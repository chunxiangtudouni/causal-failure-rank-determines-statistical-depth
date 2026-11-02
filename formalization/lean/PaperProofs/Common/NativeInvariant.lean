module

public import PaperProofs.Common.NativeProtocol
public import Mathlib.Data.List.Nodup

/-!
Bookkeeping invariants proved from the actual native transitions. These are
inductive propositions, not State fields, Step guards or postconditions.
In particular, current allocation is not silently strengthened to current
execution, and unresolved wrong outputs do not prevent later lawful steps.
-/

@[expose] public section

namespace PaperProofs.Common.Native

variable {I : Instance}

structure LedgerInvariant (C : Contract I) (L : Ledger I) (clock : ℕ) : Prop where
  wellFormed : LedgerWellFormed L
  commitment_genuine : ∀ a ∈ L.commitments,
    L.written a.handle.stage = some (!L.truth a.handle.stage) ∧
      a.handle.writeSerial = L.writeSerial a.handle.stage
  report_before_clock : ∀ i t, L.reportTime i = some t → t < clock
  commitment_before_clock : ∀ a ∈ L.commitments, a.atTime < clock
  late_report_gate : C.reporting = .late → ¬ allWritten L → ∀ i, L.reportTime i = none
  report_written : ∀ i t, L.reportTime i = some t → L.written i ≠ none

def Invariant (C : Contract I) (s : State I) : Prop :=
  LedgerInvariant C s.ledger s.clock

/-- Changes to resource counters, completion flags, or advance timestamps do
not affect these invariants. Time may only increase. -/
theorem LedgerInvariant.frame {C : Contract I} {L L' : Ledger I} {clock clock' : ℕ}
    (h : LedgerInvariant C L clock)
    (htruth : L'.truth = L.truth) (hwritten : L'.written = L.written)
    (hserial : L'.writeSerial = L.writeSerial) (hreport : L'.reportTime = L.reportTime)
    (hcommit : L'.commitments = L.commitments) (hexecute : L'.executions = L.executions)
    (hclock : clock ≤ clock') : LedgerInvariant C L' clock' := by
  constructor
  · constructor
    · simpa only [hcommit] using h.wellFormed.commitment_tools
    · simpa only [hcommit] using h.wellFormed.commitment_stages
    · simpa only [hexecute] using h.wellFormed.execution_tools
    · simpa only [hexecute] using h.wellFormed.execution_stages
    · simpa only [hexecute] using h.wellFormed.compatible
    · simpa only [hexecute, hwritten, htruth, hserial] using h.wellFormed.genuine
    · simpa only [hcommit, hreport] using h.wellFormed.reported
    · simpa only [hexecute, hcommit] using h.wellFormed.backed
  · simpa only [hcommit, hwritten, htruth, hserial] using h.commitment_genuine
  · intro i t ht
    exact lt_of_lt_of_le (h.report_before_clock i t (hreport ▸ ht)) hclock
  · intro a ha
    exact lt_of_lt_of_le (h.commitment_before_clock a (hcommit ▸ ha)) hclock
  · simpa only [allWritten, hwritten, hreport] using h.late_report_gate
  · simpa only [hreport, hwritten] using h.report_written

theorem initial_invariant (C : Contract I) (truth : I.Stage → Bool) :
    Invariant C (initial truth) := by
  constructor
  · constructor <;> simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]

private theorem nodup_map_append_one {A B : Type*} (items : List A) (f : A → B) (new : A)
    (h : (items.map f).Nodup) (hfresh : ∀ old ∈ items, f old ≠ f new) :
    ((items ++ [new]).map f).Nodup := by
  rw [List.map_append, List.map_singleton, List.nodup_append]
  refine ⟨h, by simp, ?_⟩
  intro left hleft right hright
  have heq : right = f new := List.mem_singleton.mp hright
  subst right
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hleft
  exact hfresh old hold

/-- Any old genuine commitment is on an already written stage. -/
theorem LedgerInvariant.commitment_ne_open {C : Contract I} {L : Ledger I} {clock : ℕ}
    (h : LedgerInvariant C L clock) {i : I.Stage} (hopen : L.written i = none)
    {a : Commitment I} (ha : a ∈ L.commitments) : a.handle.stage ≠ i := by
  intro heq
  have hg := (h.commitment_genuine a ha).1
  rw [heq, hopen] at hg
  cases hg

theorem LedgerInvariant.execution_ne_open {C : Contract I} {L : Ledger I} {clock : ℕ}
    (h : LedgerInvariant C L clock) {i : I.Stage} (hopen : L.written i = none)
    {e : Execution I} (he : e ∈ L.executions) : e.handle.stage ≠ i := by
  intro heq
  have hg := (h.wellFormed.genuine e he).1
  rw [heq, hopen] at hg
  cases hg

theorem LedgerInvariant.no_commitments_before_late_reports {C : Contract I}
    {L : Ledger I} {clock : ℕ} (h : LedgerInvariant C L clock)
    (hlate : C.reporting = .late) (hnotWritten : ¬ allWritten L) : L.commitments = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  obtain ⟨t, ht, _⟩ := h.wellFormed.reported a ha
  rw [h.late_report_gate hlate hnotWritten a.handle.stage] at ht
  cases ht

theorem writeLedger_invariant {C : Contract I} {s : State I}
    (h : Invariant C s) (i : I.Stage) (bit : Bool) (hopen : s.ledger.written i = none) :
    LedgerInvariant C (writeLedger s i bit) s.clock := by
  constructor
  · constructor
    · exact h.wellFormed.commitment_tools
    · exact h.wellFormed.commitment_stages
    · exact h.wellFormed.execution_tools
    · exact h.wellFormed.execution_stages
    · exact h.wellFormed.compatible
    · intro e he
      have hne := h.execution_ne_open hopen he
      simpa only [writeLedger, Function.update_of_ne hne] using h.wellFormed.genuine e he
    · exact h.wellFormed.reported
    · exact h.wellFormed.backed
  · intro a ha
    have hne := h.commitment_ne_open hopen ha
    simpa only [writeLedger, Function.update_of_ne hne] using h.commitment_genuine a ha
  · exact h.report_before_clock
  · exact h.commitment_before_clock
  · intro hlate _
    exact h.late_report_gate hlate (fun hall => hall i hopen)
  · intro j t ht
    have hne : j ≠ i := by
      intro heq
      subst j
      exact h.report_written i t ht hopen
    simpa only [writeLedger, Function.update_of_ne hne] using h.report_written j t ht

theorem early_report_invariant {C : Contract I} {L : Ledger I} {clock : ℕ}
    (h : LedgerInvariant C L clock) (i : I.Stage)
    (hearly : C.reporting = .early) (hwritten : L.written i ≠ none)
    (hclear : ∀ a ∈ L.commitments, a.handle.stage ≠ i) :
    LedgerInvariant C {L with reportTime := Function.update L.reportTime i (some clock)}
      (clock + 1) := by
  constructor
  · constructor
    · exact h.wellFormed.commitment_tools
    · exact h.wellFormed.commitment_stages
    · exact h.wellFormed.execution_tools
    · exact h.wellFormed.execution_stages
    · exact h.wellFormed.compatible
    · exact h.wellFormed.genuine
    · intro a ha
      simpa only [Function.update_of_ne (hclear a ha)] using h.wellFormed.reported a ha
    · exact h.wellFormed.backed
  · exact h.commitment_genuine
  · intro j t ht
    by_cases heq : j = i
    · subst j
      simp only [Function.update_self, Option.some.injEq] at ht
      subst t
      exact Nat.lt_succ_self clock
    · have hold : L.reportTime j = some t := by
        simpa only [Function.update_of_ne heq] using ht
      exact lt_trans (h.report_before_clock j t hold) (Nat.lt_succ_self clock)
  · intro a ha
    exact lt_trans (h.commitment_before_clock a ha) (Nat.lt_succ_self clock)
  · intro hlate
    rw [hearly] at hlate
    cases hlate
  · intro j t ht
    by_cases heq : j = i
    · subst j
      exact hwritten
    · exact h.report_written j t (by simpa only [Function.update_of_ne heq] using ht)

theorem late_report_all_invariant {C : Contract I} {L : Ledger I} {clock : ℕ}
    (h : LedgerInvariant C L clock) (hclear : L.commitments = []) (hwritten : allWritten L) :
    LedgerInvariant C {L with reportTime := fun _ => some clock} (clock + 1) := by
  constructor
  · constructor
    · exact h.wellFormed.commitment_tools
    · exact h.wellFormed.commitment_stages
    · exact h.wellFormed.execution_tools
    · exact h.wellFormed.execution_stages
    · exact h.wellFormed.compatible
    · exact h.wellFormed.genuine
    · simp [hclear]
    · exact h.wellFormed.backed
  · exact h.commitment_genuine
  · intro j t ht
    have heq : clock = t := Option.some.inj ht
    subst t
    exact Nat.lt_succ_self clock
  · intro a ha
    exact lt_trans (h.commitment_before_clock a ha) (Nat.lt_succ_self clock)
  · intro _ hnot
    exact False.elim (hnot hwritten)
  · intro j _ _
    exact hwritten j

theorem reportedWriteLedger_invariant {C : Contract I} {s : State I}
    (h : Invariant C s) (i : I.Stage) (bit : Bool) (hopen : s.ledger.written i = none) :
    LedgerInvariant C (reportedWriteLedger C s i bit) (s.clock + 1) := by
  classical
  have hwrite := writeLedger_invariant h i bit hopen
  simp only [reportedWriteLedger]
  split_ifs with hearly hall
  · exact early_report_invariant hwrite i hearly (by simp [writeLedger])
      (fun a ha => h.commitment_ne_open hopen ha)
  · have hlate : C.reporting = .late := by
      cases hreport : C.reporting with
      | early => exact False.elim (hearly hreport)
      | late => rfl
    have hclear := h.no_commitments_before_late_reports hlate (fun hw => hw i hopen)
    exact late_report_all_invariant hwrite hclear hall
  · exact hwrite.frame rfl rfl rfl rfl rfl rfl (Nat.le_succ _)

theorem allocateLedger_invariant {C : Contract I} {s : State I}
    (h : Invariant C s) (handle : MismatchHandle I) (tool : I.Tool)
    (hhandle : validHandle s handle)
    (hfresh : ∀ a ∈ s.ledger.commitments, a.tool ≠ tool)
    (hstage : ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ handle.stage) :
    LedgerInvariant C (allocateLedger s handle tool) (s.clock + 1) := by
  constructor
  · constructor
    · exact nodup_map_append_one _ (fun a : Commitment I => a.tool) _
        h.wellFormed.commitment_tools hfresh
    · exact nodup_map_append_one _ (fun a : Commitment I => a.handle.stage) _
        h.wellFormed.commitment_stages hstage
    · exact h.wellFormed.execution_tools
    · exact h.wellFormed.execution_stages
    · exact h.wellFormed.compatible
    · exact h.wellFormed.genuine
    · intro a ha
      simp only [allocateLedger, List.mem_append, List.mem_singleton] at ha
      rcases ha with hold | rfl
      · exact h.wellFormed.reported a hold
      · obtain ⟨t, ht⟩ := hhandle.2.2
        exact ⟨t, ht, (h.report_before_clock handle.stage t ht).le⟩
    · intro e he
      obtain ⟨a, ha, heq, htool, htime⟩ := h.wellFormed.backed e he
      exact ⟨a, List.mem_append_left _ ha, heq, htool, htime⟩
  · intro a ha
    simp only [allocateLedger, List.mem_append, List.mem_singleton] at ha
    rcases ha with hold | rfl
    · exact h.commitment_genuine a hold
    · exact ⟨hhandle.1, hhandle.2.1⟩
  · intro i t ht
    exact lt_trans (h.report_before_clock i t ht) (Nat.lt_succ_self _)
  · intro a ha
    simp only [allocateLedger, List.mem_append, List.mem_singleton] at ha
    rcases ha with hold | rfl
    · exact lt_trans (h.commitment_before_clock a hold) (Nat.lt_succ_self _)
    · exact Nat.lt_succ_self _
  · exact h.late_report_gate
  · exact h.report_written

theorem executeLedger_invariant {C : Contract I} {s : State I}
    (h : Invariant C s) (handle : MismatchHandle I) (tool : I.Tool)
    (hhandle : validHandle s handle) (hcompatible : tool ∈ I.eligible handle.stage)
    (hcommitted : ∃ a ∈ s.ledger.commitments, a.handle = handle ∧ a.tool = tool)
    (hfresh : ∀ e ∈ s.ledger.executions, e.tool ≠ tool)
    (hstage : ∀ e ∈ s.ledger.executions, e.handle.stage ≠ handle.stage) :
    LedgerInvariant C (executeLedger s handle tool) (s.clock + 1) := by
  constructor
  · constructor
    · exact h.wellFormed.commitment_tools
    · exact h.wellFormed.commitment_stages
    · exact nodup_map_append_one _ (fun e : Execution I => e.tool) _
        h.wellFormed.execution_tools hfresh
    · exact nodup_map_append_one _ (fun e : Execution I => e.handle.stage) _
        h.wellFormed.execution_stages hstage
    · intro e he
      simp only [executeLedger, List.mem_append, List.mem_singleton] at he
      rcases he with hold | rfl
      · exact h.wellFormed.compatible e hold
      · exact hcompatible
    · intro e he
      simp only [executeLedger, List.mem_append, List.mem_singleton] at he
      rcases he with hold | rfl
      · exact h.wellFormed.genuine e hold
      · exact ⟨hhandle.1, hhandle.2.1⟩
    · exact h.wellFormed.reported
    · intro e he
      simp only [executeLedger, List.mem_append, List.mem_singleton] at he
      rcases he with hold | rfl
      · exact h.wellFormed.backed e hold
      · obtain ⟨a, ha, hhandle', htool⟩ := hcommitted
        exact ⟨a, ha, hhandle', htool, (h.commitment_before_clock a ha).le⟩
  · exact h.commitment_genuine
  · intro i t ht
    exact lt_trans (h.report_before_clock i t ht) (Nat.lt_succ_self _)
  · intro a ha
    exact lt_trans (h.commitment_before_clock a ha) (Nat.lt_succ_self _)
  · exact h.late_report_gate
  · exact h.report_written

/-- Recording visible responses only changes the separate normal-call counter. -/
theorem record_invariant {C : Contract I} (accounting : NormalAccounting I) (s : State I)
    (action : Action I) (responses : List (VisibleEvent I)) (L : Ledger I)
    (cursor : ℕ) (halted : Bool) (h : LedgerInvariant C L (s.clock + 1)) :
    Invariant C (record accounting s action responses L cursor halted) :=
  h.frame rfl rfl rfl rfl rfl rfl le_rfl

/-- Every actual transition preserves the independently established invariant. -/
theorem step_invariant (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (h : Step input C mode accounting tapes s action s') (hinv : Invariant C s) :
    Invariant C s' := by
  cases h with
  | review i _ _ _ =>
    apply record_invariant
    exact hinv.frame rfl rfl rfl rfl rfl rfl (Nat.le_succ _)
  | write i bit _ port _ =>
    exact record_invariant _ _ _ _ _ _ _ (reportedWriteLedger_invariant hinv i bit port)
  | allocate handle tool _ valid _ unused unallocated _ _ =>
    exact record_invariant _ _ _ _ _ _ _
      (allocateLedger_invariant hinv handle tool valid unused unallocated)
  | execute handle tool _ valid compatible committed unused uncorrected _ _ =>
    exact record_invariant _ _ _ _ _ _ _
      (executeLedger_invariant hinv handle tool valid compatible committed unused uncorrected)
  | advance i _ _ _ =>
    apply record_invariant
    exact hinv.frame rfl rfl rfl rfl rfl rfl (Nat.le_succ _)
  | stop _ => exact hinv.frame rfl rfl rfl rfl rfl rfl (Nat.le_succ _)
  | abandon _ => exact hinv.frame rfl rfl rfl rfl rfl rfl (Nat.le_succ _)

/-- This induction uses the actual initial state and actual Step relation. -/
theorem prefix_invariant (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (h : Prefix input C mode accounting policy seed truth tapes n s) : Invariant C s := by
  induction h with
  | initial => exact initial_invariant C truth
  | next _ step ih => exact step_invariant input C mode accounting tapes step ih

theorem prefix_ledgerWellFormed (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (h : Prefix input C mode accounting policy seed truth tapes n s) :
    LedgerWellFormed s.ledger :=
  (prefix_invariant input C mode accounting policy seed truth tapes h).wellFormed

/-! ### Finite counters at every finite prefix

The uncapped comparison allows arbitrarily long runs, but every finite
actual prefix still has finite counters. This is proved from the updates,
not imposed as a Step guard, and justifies the protocol's `reviews.toNat`.
-/

def FiniteCounters (L : Ledger I) : Prop :=
  (∀ i, L.reviews i ≠ ⊤) ∧ L.normalCalls ≠ ⊤

theorem initial_finiteCounters (truth : I.Stage → Bool) :
    FiniteCounters (initial truth).ledger := by
  constructor <;> simp [initial]

theorem record_finiteCounters (accounting : NormalAccounting I) (s : State I)
    (action : Action I) (responses : List (VisibleEvent I)) (L : Ledger I)
    (cursor : ℕ) (halted : Bool) (h : FiniteCounters L) :
    FiniteCounters (record accounting s action responses L cursor halted).ledger := by
  constructor
  · exact h.1
  · change L.normalCalls + (accounting s.history action responses : ℕ∞) ≠ ⊤
    intro htop
    rcases ENat.add_eq_top.mp htop with hleft | hright
    · exact h.2 hleft
    · exact ENat.natCast_ne_top _ hright

theorem reviewLedger_finiteCounters {s : State I} (h : FiniteCounters s.ledger)
    (i : I.Stage) : FiniteCounters (reviewLedger s i) := by
  constructor
  · intro j
    by_cases heq : j = i
    · subst j
      simp only [reviewLedger, Function.update_self]
      intro htop
      rcases ENat.add_eq_top.mp htop with hleft | hright
      · exact h.1 i hleft
      · exact ENat.natCast_ne_top 1 hright
    · simpa only [reviewLedger, Function.update_of_ne heq] using h.1 j
  · exact h.2

theorem step_finiteCounters (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (h : Step input C mode accounting tapes s action s') (hfinite : FiniteCounters s.ledger) :
    FiniteCounters s'.ledger := by
  cases h with
  | review i _ _ _ =>
    exact record_finiteCounters _ _ _ _ _ _ _ (reviewLedger_finiteCounters hfinite i)
  | write i bit _ _ _ =>
    apply record_finiteCounters
    classical
    simp only [reportedWriteLedger]
    split_ifs <;> exact hfinite
  | allocate _ _ _ _ _ _ _ _ _ =>
    exact record_finiteCounters _ _ _ _ _ _ _ hfinite
  | execute _ _ _ _ _ _ _ _ _ _ =>
    exact record_finiteCounters _ _ _ _ _ _ _ hfinite
  | advance _ _ _ _ => exact record_finiteCounters _ _ _ _ _ _ _ hfinite
  | stop _ => exact hfinite
  | abandon _ => exact hfinite

theorem prefix_finiteCounters (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (h : Prefix input C mode accounting policy seed truth tapes n s) :
    FiniteCounters s.ledger := by
  induction h with
  | initial => exact initial_finiteCounters truth
  | next _ step ih => exact step_finiteCounters input C mode accounting tapes step ih

theorem prefix_reviews_finite (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (h : Prefix input C mode accounting policy seed truth tapes n s) (i : I.Stage) :
    s.ledger.reviews i ≠ ⊤ :=
  (prefix_finiteCounters input C mode accounting policy seed truth tapes h).1 i

theorem prefix_normalCalls_finite (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (h : Prefix input C mode accounting policy seed truth tapes n s) :
    s.ledger.normalCalls ≠ ⊤ :=
  (prefix_finiteCounters input C mode accounting policy seed truth tapes h).2

theorem prefix_reviews_natCast_toNat (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (h : Prefix input C mode accounting policy seed truth tapes n s) (i : I.Stage) :
    ((s.ledger.reviews i).toNat : ℕ∞) = s.ledger.reviews i :=
  ENat.natCast_toNat (prefix_reviews_finite input C mode accounting policy seed truth tapes h i)

end PaperProofs.Common.Native
