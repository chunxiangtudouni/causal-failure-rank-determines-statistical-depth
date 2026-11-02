module

public import PaperProofs.Common.NativeRun
import Lean.Elab.Tactic.Omega

/-!
Deadlines proved from actual transitions, rather than imposed on successful
states. The final theorem identifies the existing ledger success predicate
with physical correctness on every actual prefix. Thus its window clauses
do not silently strengthen the native task-success event.
-/

@[expose] public section

namespace PaperProofs.Common.Native

variable {I : Instance}

structure DeadlineInvariant (C : Contract I) (L : Ledger I) (cursor clock : ℕ) : Prop where
  advance_cursor : ∀ i t, L.advanceTime i = some t → i.val < cursor
  advance_clock : ∀ i t, L.advanceTime i = some t → t < clock
  commitment_clock : ∀ a ∈ L.commitments, a.atTime < clock
  execution_clock : ∀ e ∈ L.executions, e.atTime < clock
  commitment_deadline : C.allocation = .currentWindow → ∀ a ∈ L.commitments,
    ∀ t, L.advanceTime a.handle.stage = some t → a.atTime < t
  execution_deadline : C.execution = .currentWindow → ∀ e ∈ L.executions,
    ∀ t, L.advanceTime e.handle.stage = some t → e.atTime < t

theorem DeadlineInvariant.frame {C : Contract I} {L L' : Ledger I}
    {cursor cursor' clock clock' : ℕ} (h : DeadlineInvariant C L cursor clock)
    (ha : L'.advanceTime = L.advanceTime) (hc : L'.commitments = L.commitments)
    (he : L'.executions = L.executions) (hcursor : cursor ≤ cursor') (hclock : clock ≤ clock') :
    DeadlineInvariant C L' cursor' clock' := by
  constructor
  · intro i t ht
    exact lt_of_lt_of_le (h.advance_cursor i t (ha ▸ ht)) hcursor
  · intro i t ht
    exact lt_of_lt_of_le (h.advance_clock i t (ha ▸ ht)) hclock
  · intro a hm
    exact lt_of_lt_of_le (h.commitment_clock a (hc ▸ hm)) hclock
  · intro e hm
    exact lt_of_lt_of_le (h.execution_clock e (he ▸ hm)) hclock
  · simpa only [ha, hc] using h.commitment_deadline
  · simpa only [ha, he] using h.execution_deadline

theorem initial_deadlineInvariant (C : Contract I) (truth : I.Stage → Bool) :
    DeadlineInvariant C (initial truth).ledger (initial truth).cursor (initial truth).clock := by
  constructor <;> simp [initial]

theorem allocate_deadlineInvariant {C : Contract I} {s : State I}
    (h : DeadlineInvariant C s.ledger s.cursor s.clock)
    (handle : MismatchHandle I) (r : I.Tool) (hw : allocationOpen C s handle.stage) :
    DeadlineInvariant C (allocateLedger s handle r) s.cursor (s.clock + 1) := by
  constructor
  · exact h.advance_cursor
  · intro i t ht
    exact (h.advance_clock i t ht).trans_le (Nat.le_succ _)
  · intro a hm
    simp only [allocateLedger, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact (h.commitment_clock a hm).trans_le (Nat.le_succ _)
    · exact Nat.lt_succ_self _
  · intro e hm
    exact (h.execution_clock e hm).trans_le (Nat.le_succ _)
  · intro hC a hm t ht
    simp only [allocateLedger, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h.commitment_deadline hC a hm t ht
    · have hcur := hw hC
      have hpast := h.advance_cursor handle.stage t ht
      omega
  · exact h.execution_deadline

theorem execute_deadlineInvariant {C : Contract I} {s : State I}
    (h : DeadlineInvariant C s.ledger s.cursor s.clock)
    (handle : MismatchHandle I) (r : I.Tool) (hw : executionOpen C s handle.stage) :
    DeadlineInvariant C (executeLedger s handle r) s.cursor (s.clock + 1) := by
  constructor
  · exact h.advance_cursor
  · intro i t ht
    exact (h.advance_clock i t ht).trans_le (Nat.le_succ _)
  · intro a hm
    exact (h.commitment_clock a hm).trans_le (Nat.le_succ _)
  · intro e hm
    simp only [executeLedger, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact (h.execution_clock e hm).trans_le (Nat.le_succ _)
    · exact Nat.lt_succ_self _
  · exact h.commitment_deadline
  · intro hC e hm t ht
    simp only [executeLedger, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h.execution_deadline hC e hm t ht
    · have hcur := hw hC
      have hpast := h.advance_cursor handle.stage t ht
      omega

theorem advance_deadlineInvariant {C : Contract I} {s : State I}
    (h : DeadlineInvariant C s.ledger s.cursor s.clock) (i : I.Stage)
    (hcur : s.cursor = i.val) :
    DeadlineInvariant C (advanceLedger s i) (s.cursor + 1) (s.clock + 1) := by
  constructor
  · intro j t ht
    by_cases hji : j = i
    · subst j
      simp only [advanceLedger, Function.update_self, Option.some.injEq] at ht
      omega
    · have hold : s.ledger.advanceTime j = some t := by
        simpa only [advanceLedger, Function.update_of_ne hji] using ht
      exact (h.advance_cursor j t hold).trans_le (Nat.le_succ _)
  · intro j t ht
    by_cases hji : j = i
    · subst j
      simp only [advanceLedger, Function.update_self, Option.some.injEq] at ht
      omega
    · have hold : s.ledger.advanceTime j = some t := by
        simpa only [advanceLedger, Function.update_of_ne hji] using ht
      exact (h.advance_clock j t hold).trans_le (Nat.le_succ _)
  · intro a hm
    exact (h.commitment_clock a hm).trans_le (Nat.le_succ _)
  · intro e hm
    exact (h.execution_clock e hm).trans_le (Nat.le_succ _)
  · intro hC a hm t ht
    by_cases hai : a.handle.stage = i
    · have heq : s.clock = t := by simpa only [advanceLedger, hai, Function.update_self,
        Option.some.injEq] using ht
      simpa only [← heq] using h.commitment_clock a hm
    · exact h.commitment_deadline hC a hm t (by
        simpa only [advanceLedger, Function.update_of_ne hai] using ht)
  · intro hC e hm t ht
    by_cases hei : e.handle.stage = i
    · have heq : s.clock = t := by simpa only [advanceLedger, hei, Function.update_self,
        Option.some.injEq] using ht
      simpa only [← heq] using h.execution_clock e hm
    · exact h.execution_deadline hC e hm t (by
        simpa only [advanceLedger, Function.update_of_ne hei] using ht)

theorem step_deadlineInvariant (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (h : DeadlineInvariant C s.ledger s.cursor s.clock)
    (hs : Step input C mode accounting tapes s action s') :
    DeadlineInvariant C s'.ledger s'.cursor s'.clock := by
  cases hs with
  | review => exact h.frame rfl rfl rfl le_rfl (Nat.le_succ _)
  | write i bit _ _ _ =>
    classical
    simp only [record, reportedWriteLedger]
    split_ifs <;> exact h.frame rfl rfl rfl le_rfl (Nat.le_succ _)
  | allocate handle r _ _ _ _ _ window _ =>
    exact (allocate_deadlineInvariant h handle r window).frame rfl rfl rfl le_rfl le_rfl
  | execute handle r _ _ _ _ _ _ window _ =>
    exact (execute_deadlineInvariant h handle r window).frame rfl rfl rfl le_rfl le_rfl
  | advance i live _ _ =>
    exact (advance_deadlineInvariant h i live.2).frame rfl rfl rfl le_rfl le_rfl
  | stop => exact h.frame rfl rfl rfl le_rfl (Nat.le_succ _)
  | abandon => exact h.frame rfl rfl rfl le_rfl (Nat.le_succ _)

theorem prefix_deadlineInvariant (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    DeadlineInvariant C s.ledger s.cursor s.clock := by
  induction hp with
  | initial => exact initial_deadlineInvariant C truth
  | next _ hs ih => exact step_deadlineInvariant input C mode accounting tapes ih hs

/-- Genuine executions physically repair exactly their own required output. -/
noncomputable def finalOutput (L : Ledger I) (i : I.Stage) : Option Bool := by
  classical
  exact if ∃ e ∈ L.executions, e.handle.stage = i then some (L.truth i) else L.written i

def PhysicalSuccess (L : Ledger I) : Prop :=
  L.finished = true ∧ L.abandoned = false ∧ ∀ i, finalOutput L i = some (L.truth i)

theorem finalOutput_correct_iff (L : Ledger I) (i : I.Stage) :
    finalOutput L i = some (L.truth i) ↔
      L.written i = some (L.truth i) ∨ ∃ e ∈ L.executions, e.handle.stage = i := by
  classical
  unfold finalOutput
  split_ifs with h
  · simp [h]
  · simp [h]

theorem success_iff_physical {C : Contract I} {L : Ledger I} {cursor clock : ℕ}
    (hwf : LedgerWellFormed L) (htime : DeadlineInvariant C L cursor clock) :
    L.success C ↔ PhysicalSuccess L := by
  constructor
  · rintro ⟨hf, ha, _, hcorrect⟩
    exact ⟨hf, ha, fun i ↦ (finalOutput_correct_iff L i).mpr (hcorrect i)⟩
  · rintro ⟨hf, ha, hphysical⟩
    have hcorrect (i : I.Stage) := (finalOutput_correct_iff L i).mp (hphysical i)
    refine ⟨hf, ha, ?_, hcorrect⟩
    intro i t hadv hwrong
    obtain hright | ⟨e, he, hei⟩ := hcorrect i
    · rw [hwrong] at hright
      cases htruth : L.truth i <;> simp [htruth] at hright
    · constructor
      · intro hC
        obtain ⟨a, halloc, hhandle, htool, _⟩ := hwf.backed e he
        have hai : a.handle.stage = i := by rw [hhandle]; exact hei
        exact ⟨a, halloc, hai, htime.commitment_deadline hC a halloc t (by simpa [hai] using hadv)⟩
      · intro hC
        exact ⟨e, he, hei, htime.execution_deadline hC e he t (by simpa [hei] using hadv)⟩

theorem prefix_success_iff_physical (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    s.ledger.success C ↔ PhysicalSuccess s.ledger :=
  success_iff_physical (prefix_ledgerWellFormed input C mode accounting policy seed truth tapes hp)
    (prefix_deadlineInvariant input C mode accounting policy seed truth tapes hp)

theorem run_success_iff_physical (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting policy)
    (sample : Seed × input.World) (n : ℕ) :
    (run input C mode accounting policy sample n).ledger.success C ↔
      PhysicalSuccess (run input C mode accounting policy sample n).ledger := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C mode accounting policy hlegal sample n
  exact prefix_success_iff_physical input C mode accounting policy sample.1 _ _ hp

end PaperProofs.Common.Native
