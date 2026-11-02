module

public import PaperProofs.Structure.PA17_TerminalRow_002

/-! Exact stored-row recurrence, then an actual reverse-stage/positive-budget
flatMap schedule. The schedule theorem is explicitly conditional on a local
physical single-cell execution contract. It supplies no A17 implementation
existence, generation, capacity/word safety or resource claim. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17RowSchedule004

open IndexedRAM IndexedClosureRAM AlgorithmClaims

variable {Tool : Type*}

theorem rowsList_step [DecidableEq Tool] (cache : IndexedNodeCache Tool) (maxBudget : Nat)
    (suffix : List (Finset Tool)) (stage : Nat) (hstage : stage < suffix.length) :
    (IndexedTable.rowsList cache maxBudget suffix)[stage]'(by
      rw [IndexedTable.rowsList_length]; omega) =
    IndexedTable.rowStep cache maxBudget suffix[stage]
      ((IndexedTable.rowsList cache maxBudget suffix)[stage + 1]'(by
        rw [IndexedTable.rowsList_length]; omega)) := by
  induction suffix generalizing stage with
  | nil => simp only [List.length_nil] at hstage; omega
  | cons eligible later ih =>
    cases stage with
    | zero => rfl
    | succ stage =>
      simpa only [IndexedTable.rowsList, IndexedTable.rows, List.getElem_cons_succ] using
        ih stage (by simpa only [List.length_cons] using Nat.lt_of_succ_lt_succ hstage)

theorem storedPositiveRow_step (q : Nat) (full : List (Finset (Fin q))) (stage : Fin full.length) :
    IndexedQuery.storedPositiveRow q full ⟨stage.val, by omega⟩ =
      IndexedTable.rowStep (prepareNormalization q full).indexed (q + 1) full[stage.val]
        (IndexedQuery.storedPositiveRow q full ⟨stage.val + 1, by omega⟩) := by
  simpa only [IndexedQuery.storedPositiveRow, IndexedTable.buildPositive, List.getElem_toArray] using
    rowsList_step (prepareNormalization q full).indexed (q + 1) full stage.val stage.isLt

theorem storedPositiveRow_cell (q : Nat) (full : List (Finset (Fin q))) (stage : Fin full.length)
    (budget : Fin (q + 2)) (hbudget : 0 < budget.val) :
    (IndexedQuery.storedPositiveRow q full ⟨stage.val, by omega⟩).get budget =
      IndexedEntry.cell (prepareNormalization q full).indexed full[stage.val]
        ((IndexedQuery.storedPositiveRow q full ⟨stage.val + 1, by omega⟩).get budget)
        ((IndexedQuery.storedPositiveRow q full ⟨stage.val + 1, by omega⟩).get
          ⟨budget.val - 1, by omega⟩) := by
  rw [storedPositiveRow_step, IndexedTable.rowStep_get]
  simp only [IndexedEntry.budgetCell, show budget.val ≠ 0 by omega, ite_false]
  rfl

theorem storedPositiveRow_terminal (q : Nat) (full : List (Finset (Fin q))) (budget : Fin (q + 2)) :
    (IndexedQuery.storedPositiveRow q full ⟨full.length, by omega⟩).get budget =
      IndexedEntry.free (prepareNormalization q full).indexed := by
  rw [PA17TerminalRow002.storedPositiveRow_terminal, IndexedTable.terminalRow_get]

theorem storedPositiveRow_budgetZero (q : Nat) (full : List (Finset (Fin q)))
    (stage : Fin (full.length + 1)) :
    (IndexedQuery.storedPositiveRow q full stage).get ⟨0, by omega⟩ =
      IndexedEntry.free (prepareNormalization q full).indexed :=
  PA17TerminalRow002.storedPositiveRow_budgetZero q full stage

def positiveBudgets (q : Nat) : List Nat := (List.range (q + 1)).map (fun index => index + 1)

def rowProgram (cellProgram : Nat → Nat → List Op) (q stage : Nat) : List Op :=
  (positiveBudgets q).flatMap (cellProgram stage)

def scheduleProgram (cellProgram : Nat → Nat → List Op) (N q : Nat) : List Op :=
  (List.range N).reverse.flatMap (rowProgram cellProgram q)

theorem positiveBudgets_mem (q budget : Nat) : budget ∈ positiveBudgets q ↔ 0 < budget ∧ budget < q + 2 := by
  constructor
  · intro hm
    obtain ⟨index, hi, rfl⟩ := List.mem_map.mp hm
    have := List.mem_range.mp hi
    omega
  · rintro ⟨hpos, hb⟩
    exact List.mem_map.mpr ⟨budget - 1, List.mem_range.mpr (by omega), by omega⟩

def slot (q stage budget : Nat) : Nat := stage * (q + 2) + budget

def CellCorrect (q : Nat) (full : List (Finset (Fin q))) (state : State)
    (stage : Fin (full.length + 1)) (budget : Fin (q + 2)) : Prop :=
  readEntry (prepareNormalization q full).indexed.nodes.size (slot q stage.val budget.val) state.heap =
    (IndexedQuery.storedPositiveRow q full stage).get budget

def RowReady (q : Nat) (full : List (Finset (Fin q))) (state : State)
    (stage : Fin (full.length + 1)) : Prop := ∀ budget : Fin (q + 2), CellCorrect q full state stage budget

def RowsFrom (q : Nat) (full : List (Finset (Fin q))) (first : Nat) (state : State) : Prop :=
  ∀ stage : Fin (full.length + 1), first ≤ stage.val → RowReady q full state stage

def ZeroReady (q : Nat) (full : List (Finset (Fin q))) (state : State) : Prop :=
  ∀ stage : Fin (full.length + 1), CellCorrect q full state stage ⟨0, by omega⟩

def PreservesCorrect (q : Nat) (full : List (Finset (Fin q))) (before after : State) : Prop :=
  ∀ stage budget, CellCorrect q full before stage budget → CellCorrect q full after stage budget

/-! Local contract deliberately returns the original algebraic operation on
the entries read from the incoming persistent heap. Stored-row answers, rank,
future trace, and correctness of completed rows are not contract premises.
The invariant parameter records concrete metadata/workspace conditions and
must be independently instantiated and proved preserved by the caller. -/

def SingleCellContract (q : Nat) (full : List (Finset (Fin q)))
    (rom : ROM) (cellProgram : Nat → Nat → List Op) (invariant : State → Prop) : Prop :=
  ∀ (stage : Fin full.length) (budget : Fin (q + 2)), 0 < budget.val →
    ∀ state : State, invariant state →
    let result := execute rom (cellProgram stage.val budget.val) state
    invariant result ∧
      readEntry (prepareNormalization q full).indexed.nodes.size (slot q stage.val budget.val) result.heap =
        IndexedEntry.cell (prepareNormalization q full).indexed full[stage.val]
          (readEntry (prepareNormalization q full).indexed.nodes.size (slot q (stage.val + 1) budget.val) state.heap)
          (readEntry (prepareNormalization q full).indexed.nodes.size (slot q (stage.val + 1) (budget.val - 1)) state.heap) ∧
      (∀ (otherStage : Fin (full.length + 1)) (otherBudget : Fin (q + 2)),
        otherStage.val ≠ stage.val ∨ otherBudget.val ≠ budget.val →
          readEntry (prepareNormalization q full).indexed.nodes.size (slot q otherStage.val otherBudget.val) result.heap =
            readEntry (prepareNormalization q full).indexed.nodes.size (slot q otherStage.val otherBudget.val) state.heap)

theorem cellStep_correct (q : Nat) (full : List (Finset (Fin q))) (rom : ROM)
    (cellProgram : Nat → Nat → List Op) (invariant : State → Prop)
    (hcontract : SingleCellContract q full rom cellProgram invariant)
    (stage : Fin full.length) (budget : Fin (q + 2)) (hbudget : 0 < budget.val)
    (state : State) (hinvariant : invariant state)
    (hnext : RowReady q full state ⟨stage.val + 1, by omega⟩) :
    CellCorrect q full (execute rom (cellProgram stage.val budget.val) state) ⟨stage.val, by omega⟩ budget := by
  have hc := (hcontract stage budget hbudget state hinvariant).2.1
  unfold CellCorrect
  rw [hc, hnext budget, hnext ⟨budget.val - 1, by omega⟩, storedPositiveRow_cell q full stage budget hbudget]

theorem cellStep_preservesCorrect (q : Nat) (full : List (Finset (Fin q))) (rom : ROM)
    (cellProgram : Nat → Nat → List Op) (invariant : State → Prop)
    (hcontract : SingleCellContract q full rom cellProgram invariant)
    (stage : Fin full.length) (budget : Fin (q + 2)) (hbudget : 0 < budget.val)
    (state : State) (hinvariant : invariant state)
    (hnext : RowReady q full state ⟨stage.val + 1, by omega⟩) :
    PreservesCorrect q full state (execute rom (cellProgram stage.val budget.val) state) := by
  intro otherStage otherBudget hcorrect
  by_cases hs : otherStage.val = stage.val
  · by_cases hb : otherBudget.val = budget.val
    · have hse : otherStage = (⟨stage.val, by omega⟩ : Fin (full.length + 1)) := Fin.ext hs
      have hbe : otherBudget = budget := Fin.ext hb
      rw [hse, hbe]
      exact cellStep_correct q full rom cellProgram invariant hcontract stage budget hbudget state hinvariant hnext
    · exact ((hcontract stage budget hbudget state hinvariant).2.2 otherStage otherBudget (Or.inr hb)).trans hcorrect
  · exact ((hcontract stage budget hbudget state hinvariant).2.2 otherStage otherBudget (Or.inl hs)).trans hcorrect

theorem budgetList_correct (q : Nat) (full : List (Finset (Fin q))) (rom : ROM)
    (cellProgram : Nat → Nat → List Op) (invariant : State → Prop)
    (hcontract : SingleCellContract q full rom cellProgram invariant)
    (stage : Fin full.length) (budgets : List Nat)
    (hbudgets : ∀ budget ∈ budgets, 0 < budget ∧ budget < q + 2)
    (state : State) (hinvariant : invariant state)
    (hnext : RowReady q full state ⟨stage.val + 1, by omega⟩) :
    let result := execute rom (budgets.flatMap (cellProgram stage.val)) state
    invariant result ∧ PreservesCorrect q full state result ∧
      ∀ (budget : Nat) (hb : budget ∈ budgets),
        CellCorrect q full result ⟨stage.val, by omega⟩ ⟨budget, (hbudgets budget hb).2⟩ := by
  induction budgets generalizing state with
  | nil => exact ⟨hinvariant, fun _ _ h => h, by intro budget hb; cases hb⟩
  | cons head later ih =>
    have hb := hbudgets head List.mem_cons_self
    let after := execute rom (cellProgram stage.val head) state
    have hi : invariant after := (hcontract stage ⟨head, hb.2⟩ hb.1 state hinvariant).1
    have hp : PreservesCorrect q full state after :=
      cellStep_preservesCorrect q full rom cellProgram invariant hcontract stage ⟨head, hb.2⟩ hb.1 state hinvariant hnext
    have hc : CellCorrect q full after ⟨stage.val, by omega⟩ ⟨head, hb.2⟩ :=
      cellStep_correct q full rom cellProgram invariant hcontract stage ⟨head, hb.2⟩ hb.1 state hinvariant hnext
    have ht := ih (fun budget hm => hbudgets budget (List.mem_cons_of_mem _ hm)) after hi
      (fun budget => hp _ _ (hnext budget))
    dsimp only at ht ⊢
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    refine ⟨ht.1, fun otherStage otherBudget ho => ht.2.1 _ _ (hp _ _ ho), ?_⟩
    intro budget hm
    rcases List.mem_cons.mp hm with heq | hlater
    · subst budget
      exact ht.2.1 _ _ hc
    · exact ht.2.2 budget hlater

theorem rowProgram_correct (q : Nat) (full : List (Finset (Fin q))) (rom : ROM)
    (cellProgram : Nat → Nat → List Op) (invariant : State → Prop)
    (hcontract : SingleCellContract q full rom cellProgram invariant)
    (stage : Fin full.length) (state : State) (hinvariant : invariant state)
    (hzero : ZeroReady q full state) (hrows : RowsFrom q full (stage.val + 1) state) :
    let result := execute rom (rowProgram cellProgram q stage.val) state
    invariant result ∧ PreservesCorrect q full state result ∧ RowsFrom q full stage.val result := by
  have ht := budgetList_correct q full rom cellProgram invariant hcontract stage (positiveBudgets q)
    (fun budget hb => (positiveBudgets_mem q budget).mp hb) state hinvariant (hrows _ le_rfl)
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro otherStage hs budget
  by_cases heq : otherStage.val = stage.val
  · by_cases hz : budget.val = 0
    · have hb : budget = (⟨0, by omega⟩ : Fin (q + 2)) := Fin.ext hz
      rw [hb]
      exact ht.2.1 _ _ (hzero otherStage)
    · have hse : otherStage = (⟨stage.val, by omega⟩ : Fin (full.length + 1)) := Fin.ext heq
      rw [hse]
      exact ht.2.2 budget.val ((positiveBudgets_mem q budget.val).mpr ⟨by omega, budget.isLt⟩)
  · exact ht.2.1 _ _ (hrows otherStage (by omega) budget)

theorem scheduleProgram_correct (q : Nat) (full : List (Finset (Fin q))) (rom : ROM)
    (cellProgram : Nat → Nat → List Op) (invariant : State → Prop)
    (hcontract : SingleCellContract q full rom cellProgram invariant)
    (count : Nat) (hcount : count ≤ full.length) (state : State) (hinvariant : invariant state)
    (hzero : ZeroReady q full state) (hrows : RowsFrom q full count state) :
    let result := execute rom (scheduleProgram cellProgram count q) state
    invariant result ∧ PreservesCorrect q full state result ∧ RowsFrom q full 0 result := by
  induction count generalizing state with
  | zero => exact ⟨hinvariant, fun _ _ h => h, hrows⟩
  | succ count ih =>
    have hstage : count < full.length := by omega
    have hr := rowProgram_correct q full rom cellProgram invariant hcontract ⟨count, hstage⟩ state hinvariant hzero hrows
    let after := execute rom (rowProgram cellProgram q count) state
    have ht := ih (by omega) after hr.1 (fun stage => hr.2.1 _ _ (hzero stage)) hr.2.2
    dsimp only at ht ⊢
    have hprogram : scheduleProgram cellProgram (count + 1) q =
        rowProgram cellProgram q count ++ scheduleProgram cellProgram count q := by
      simp only [scheduleProgram, List.range_succ, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    rw [hprogram, IndexedClosureRAM.execute_append]
    exact ⟨ht.1, fun stage budget hc => ht.2.1 _ _ (hr.2.1 _ _ hc), ht.2.2⟩

theorem full_schedule_correct (q : Nat) (full : List (Finset (Fin q))) (rom : ROM)
    (cellProgram : Nat → Nat → List Op) (invariant : State → Prop)
    (hcontract : SingleCellContract q full rom cellProgram invariant)
    (state : State) (hinvariant : invariant state) (hzero : ZeroReady q full state)
    (hterminal : RowReady q full state ⟨full.length, by omega⟩) :
    let result := execute rom (scheduleProgram cellProgram full.length q) state
    invariant result ∧ PreservesCorrect q full state result ∧
      ∀ stage : Fin (full.length + 1), RowReady q full result stage := by
  have hr : RowsFrom q full full.length state := by
    intro stage hs
    have heq : stage = (⟨full.length, by omega⟩ : Fin (full.length + 1)) := Fin.ext (by
      change stage.val = full.length
      omega)
    simpa only [heq] using hterminal
  have ht := scheduleProgram_correct q full rom cellProgram invariant hcontract full.length le_rfl state hinvariant hzero hr
  exact ⟨ht.1, ht.2.1, fun stage => ht.2.2 stage (Nat.zero_le _)⟩

theorem prepared_seed_boundaries (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State) :
    let cache := (prepareNormalization q full).indexed
    let result := execute (givenTreeROM q full).semantic (PA17TerminalRow002.program full.length q cache.nodes.size) state
    ZeroReady q full result ∧ RowReady q full result ⟨full.length, by omega⟩ := by
  constructor
  · exact PA17TerminalRow002.prepared_program_budgetZero_stored q full hq hlaminar state
  · exact PA17TerminalRow002.prepared_program_terminal_stored q full hq hlaminar state

theorem seeded_schedule_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (cellProgram : Nat → Nat → List Op) (invariant : State → Prop)
    (hcontract : SingleCellContract q full (givenTreeROM q full).semantic cellProgram invariant)
    (state : State)
    (hinvariant : invariant (execute (givenTreeROM q full).semantic
      (PA17TerminalRow002.program full.length q (prepareNormalization q full).indexed.nodes.size) state)) :
    let cache := (prepareNormalization q full).indexed
    let result := execute (givenTreeROM q full).semantic
      (PA17TerminalRow002.program full.length q cache.nodes.size ++ scheduleProgram cellProgram full.length q) state
    invariant result ∧ ∀ stage : Fin (full.length + 1), RowReady q full result stage := by
  have hb := prepared_seed_boundaries q full hq hlaminar state
  have ht := full_schedule_correct q full (givenTreeROM q full).semantic cellProgram invariant hcontract _ hinvariant hb.1 hb.2
  dsimp only
  rw [IndexedClosureRAM.execute_append]
  exact ⟨ht.1, ht.2.2⟩

theorem positiveBudgets_length (q : Nat) : (positiveBudgets q).length = q + 1 := by
  rw [positiveBudgets, List.length_map, List.length_range]

theorem rowProgram_trace_length (cellProgram : Nat → Nat → List Op) (q stage : Nat) :
    (trace (rowProgram cellProgram q stage)).length =
      ((positiveBudgets q).map (fun budget => (trace (cellProgram stage budget)).length)).sum := by
  rw [rowProgram, UniformNormalizationRAM.trace_flatMap_length]

theorem scheduleProgram_trace_length (cellProgram : Nat → Nat → List Op) (N q : Nat) :
    (trace (scheduleProgram cellProgram N q)).length =
      ((List.range N).reverse.map (fun stage =>
        ((positiveBudgets q).map (fun budget => (trace (cellProgram stage budget)).length)).sum)).sum := by
  rw [scheduleProgram, UniformNormalizationRAM.trace_flatMap_length]
  simp only [rowProgram_trace_length]

theorem sum_map_le_mul_length {α : Type*} (entries : List α) (cost : α → Nat) (bound : Nat)
    (hcost : ∀ entry ∈ entries, cost entry ≤ bound) : (entries.map cost).sum ≤ entries.length * bound := by
  induction entries with
  | nil => exact Nat.zero_le _
  | cons head later ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm (later.length * bound)]
    exact Nat.add_le_add (hcost head List.mem_cons_self) (ih (fun entry he => hcost entry (List.mem_cons_of_mem _ he)))

theorem rowProgram_trace_le (cellProgram : Nat → Nat → List Op) (q stage bound : Nat)
    (hcost : ∀ budget, 0 < budget → budget < q + 2 → (trace (cellProgram stage budget)).length ≤ bound) :
    (trace (rowProgram cellProgram q stage)).length ≤ (q + 1) * bound := by
  rw [rowProgram_trace_length, ← positiveBudgets_length q]
  apply sum_map_le_mul_length
  intro budget hb
  have hh := (positiveBudgets_mem q budget).mp hb
  exact hcost budget hh.1 hh.2

theorem scheduleProgram_trace_le (cellProgram : Nat → Nat → List Op) (N q bound : Nat)
    (hcost : ∀ stage < N, ∀ budget, 0 < budget → budget < q + 2 →
      (trace (cellProgram stage budget)).length ≤ bound) :
    (trace (scheduleProgram cellProgram N q)).length ≤ N * ((q + 1) * bound) := by
  rw [scheduleProgram, UniformNormalizationRAM.trace_flatMap_length]
  have hh := sum_map_le_mul_length (List.range N).reverse
    (fun stage => (trace (rowProgram cellProgram q stage)).length) ((q + 1) * bound) (by
      intro stage hs
      apply rowProgram_trace_le
      exact hcost stage (List.mem_range.mp (List.mem_reverse.mp hs)))
  simpa only [List.length_reverse, List.length_range] using hh

theorem scheduleProgram_halting (rom : ROM) (cellProgram : Nat → Nat → List Op) (N q bound : Nat)
    (hcost : ∀ stage < N, ∀ budget, 0 < budget → budget < q + 2 →
      (trace (cellProgram stage budget)).length ≤ bound)
    (state : State) (hpc : state.pc = 0) :
    HaltingRuns rom (scheduleProgram cellProgram N q) state (execute rom (scheduleProgram cellProgram N q) state)
      (trace (scheduleProgram cellProgram N q) ++ haltTrace) ∧
      (trace (scheduleProgram cellProgram N q) ++ haltTrace).length ≤ N * ((q + 1) * bound) + 6 := by
  refine ⟨execute_halts _ _ state hpc, ?_⟩
  rw [List.length_append, haltTrace_length]
  exact Nat.add_le_add_right (scheduleProgram_trace_le cellProgram N q bound hcost) 6

end PaperProofs.Structure.LaminarTree.PA17RowSchedule004
