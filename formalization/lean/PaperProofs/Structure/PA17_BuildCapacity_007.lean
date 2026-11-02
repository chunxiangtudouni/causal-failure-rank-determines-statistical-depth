module

public import PaperProofs.Structure.PA17_TableBuild_005
public import PaperProofs.Structure.PA17_CellSafety_006

/-! Full-build physical capacity invariants, including every VOID payload.
Concrete cell-prefix safety is composed through the real reverse-stage and
positive-budget flatMap schedule. Generic helpers are not separate A17 claims;
the final build theorem has no supplied physical bounds or safety certificate. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17BuildCapacity007

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001

def PhysicalCardBounded (q : Nat) (full : List (Finset (Fin q))) (heap : Nat → Nat) : Prop :=
  let cache := (prepareNormalization q full).indexed
  ∀ slot < cells full.length q, ∀ node : cache.NodeId,
    heap (slot * (cache.nodes.size + 1) + 1 + node.val) ≤ (cache.decode node).card

def Invariant (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (state : State) : Prop :=
  PA17TableBuild005.Invariant q full hq state ∧
    PhysicalCardBounded q full state.heap ∧
    CapacityPrefixBounded q (PA17CellLayout003.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size) state.heap

theorem prepared_prepare_physicalCardBounded (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    PhysicalCardBounded q full (execute (givenTreeROM q full).semantic
      (PA17TablePrepare004.program full.length q size) (initial (fun _ => 0))).heap := by
  intro size slot hs node
  by_cases hm : slot ∈ PA17TerminalRow002.seedSlots full.length q
  · have hr := (PA17TablePrepare004.prepared_program_correct q full hq hlaminar (initial (fun _ => 0))).2.2 slot hm
    have hh := hr.2 node
    rw [IndexedEntry.reifyCapacity_get] at hh
    exact hh.le
  · rw [PA17TablePrepare004.program, IndexedClosureRAM.execute_append,
      PA17TerminalRow002.freeSlots_frame _ size _ _ _ (slot * (size + 1) + 1 + node.val) (by
        intro other ho index hi
        have hne : slot ≠ other := by intro he; exact hm (he ▸ ho)
        simpa only [PA17TerminalRow002.slotBase, Nat.add_assoc] using
          PA17TerminalRow002.slotBase_disjoint size slot other hne (1 + node.val) index (by have := node.isLt; omega) hi)]
    have ha : slot * (size + 1) + 1 + node.val < PA17CellLayout003.capacityWords full.length q size := by
      have hh := PA17CellLayout003.table_slot_bound full.length q size slot hs (1 + node.val) (by have := node.isLt; omega)
      have hc := PA17CellLayout003.table_le_capacityWords full.length q size
      omega
    have hf := PA17MetadataAssembly003.leading_take_frame (givenTreeROM q full).semantic full.length q size
      (PA17CellLayout003.capacityWords full.length q size)
      (PA17MetadataAssembly003.program full.length q size (PA17CellLayout003.capacityWords full.length q size)).length
      (initial (fun _ => 0)) (slot * (size + 1) + 1 + node.val) ha
    rw [List.take_length] at hf
    rw [hf]
    exact Nat.zero_le _

theorem prepared_prepare_invariant (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    Invariant q full hq (execute (givenTreeROM q full).semantic
      (PA17TablePrepare004.program full.length q size) (initial (fun _ => 0))) := by
  intro size
  refine ⟨PA17TableBuild005.prepare_invariant q full hq hlaminar,
    prepared_prepare_physicalCardBounded q full hq hlaminar, ?_⟩
  have hc := PA17TablePrepare004.prepared_program_capacityThroughout q full hq hlaminar (initial (fun _ => 0))
    (by intro address _; exact Nat.zero_le _)
  have hh := hc (PA17TablePrepare004.program full.length q (prepareNormalization q full).indexed.nodes.size).length le_rfl
  rw [List.take_length] at hh
  exact hh

theorem flatMap_capacityThroughout {α : Type*} (q words : Nat) (rom : PhysicalROM)
    (entries : List α) (block : α → List Op) (invariant : State → Prop)
    (hbound : ∀ state, invariant state → CapacityPrefixBounded q words state.heap)
    (hstep : ∀ entry ∈ entries, ∀ state, invariant state →
      invariant (execute rom.semantic (block entry) state) ∧ CapacityThroughout q words rom (block entry) state)
    (state : State) (hinvariant : invariant state) :
    invariant (execute rom.semantic (entries.flatMap block) state) ∧
      CapacityThroughout q words rom (entries.flatMap block) state := by
  induction entries generalizing state with
  | nil =>
    refine ⟨hinvariant, ?_⟩
    intro count _
    simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hbound state hinvariant
  | cons head later ih =>
    have hh := hstep head List.mem_cons_self state hinvariant
    have ht := ih (fun entry he => hstep entry (List.mem_cons_of_mem _ he)) _ hh.1
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    exact ⟨ht.1, UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hh.2 ht.2⟩

theorem schedule_capacityThroughout (q words N : Nat) (rom : PhysicalROM)
    (cellProgram : Nat → Nat → List Op) (invariant : State → Prop)
    (hbound : ∀ state, invariant state → CapacityPrefixBounded q words state.heap)
    (hstep : ∀ stage < N, ∀ budget, 0 < budget → budget < q + 2 →
      ∀ state, invariant state → invariant (execute rom.semantic (cellProgram stage budget) state) ∧
        CapacityThroughout q words rom (cellProgram stage budget) state)
    (state : State) (hinvariant : invariant state) :
    invariant (execute rom.semantic (PA17RowSchedule004.scheduleProgram cellProgram N q) state) ∧
      CapacityThroughout q words rom (PA17RowSchedule004.scheduleProgram cellProgram N q) state := by
  rw [PA17RowSchedule004.scheduleProgram]
  apply flatMap_capacityThroughout q words rom _ _ invariant hbound _ state hinvariant
  intro stage hs before hi
  rw [PA17RowSchedule004.rowProgram]
  apply flatMap_capacityThroughout q words rom _ _ invariant hbound _ before hi
  intro budget hb current hc
  have hb' := (PA17RowSchedule004.positiveBudgets_mem q budget).mp hb
  exact hstep stage (List.mem_range.mp (List.mem_reverse.mp hs)) budget hb'.1 hb'.2 current hc

theorem cell_step_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin full.length) (budget : Fin (q + 2)) (hbudget : 0 < budget.val)
    (state : State) (hinvariant : Invariant q full hq state) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let code := PA17TableBuild005.cellProgram full.length q size stage.val budget.val
    Invariant q full hq (execute (givenTreeROM q full).semantic code state) ∧
      CapacityThroughout q (PA17CellLayout003.capacityWords full.length q size) (givenTreeROM q full) code state := by
  intro size code
  let cache := (prepareNormalization q full).indexed
  let goodSlot := PA17RowSchedule004.slot q (stage.val + 1) budget.val
  let badSlot := PA17RowSchedule004.slot q (stage.val + 1) (budget.val - 1)
  let outputSlot := PA17RowSchedule004.slot q stage.val budget.val
  have hgood : goodSlot < cells full.length q :=
    PA17TableBuild005.slot_bound _ _ _ _ (by have := stage.isLt; omega) budget.isLt
  have hbad : badSlot < cells full.length q :=
    PA17TableBuild005.slot_bound _ _ _ _ (by have := stage.isLt; omega) (by omega)
  have hout : outputSlot < cells full.length q :=
    PA17TableBuild005.slot_bound _ _ _ _ (by have := stage.isLt; omega) budget.isLt
  let good := readEntry size goodSlot state.heap
  let bad := readEntry size badSlot state.heap
  have hg : TagFirstRep cache state.heap (PA17TableCell004.tableBase size goodSlot) good :=
    rep_of_readEntry cache goodSlot state.heap good (hinvariant.1.2 goodSlot hgood) rfl
  have hb : TagFirstRep cache state.heap (PA17TableCell004.tableBase size badSlot) bad :=
    rep_of_readEntry cache badSlot state.heap bad (hinvariant.1.2 badSlot hbad) rfl
  have hs := PA17CellSafety006.prepared_program_safe q full hq hlaminar goodSlot badSlot outputSlot
    hgood hbad hout stage good bad state hinvariant.1.1 hg hb hinvariant.2.2 (hinvariant.2.1 goodSlot hgood)
  have hbase := (PA17TableBuild005.singleCellContract q full hq hlaminar stage budget hbudget state hinvariant.1).1
  have hphysical : PhysicalCardBounded q full (execute (givenTreeROM q full).semantic code state).heap := by
    intro other ho node
    by_cases heq : other = outputSlot
    · subst other
      exact hs.2.1 node
    · have hf := PA17TableCell004.prepared_program_frame q full hq hlaminar goodSlot badSlot outputSlot
        stage state hinvariant.1.1 (other * (size + 1) + 1 + node.val)
        (Or.inl (by
          simpa only [Nat.add_assoc] using PA17CellLayout003.table_slot_bound full.length q size other ho
            (1 + node.val) (by have := node.isLt; omega)))
        (by
          intro index hi
          simpa only [PA17TableCell004.tableBase, Nat.add_assoc] using
            PA17TableCell004.tableSlots_disjoint size other outputSlot heq (1 + node.val) (by have := node.isLt; omega) index hi)
      change (execute (givenTreeROM q full).semantic
        (PA17TableCell004.program full.length q size goodSlot badSlot outputSlot stage.val) state).heap _ ≤ _
      rw [hf]
      exact hinvariant.2.1 other ho node
  refine ⟨⟨hbase, hphysical, ?_⟩, hs.1⟩
  have hf := hs.1 (PA17TableCell004.program full.length q (prepareNormalization q full).indexed.nodes.size
    goodSlot badSlot outputSlot stage.val).length le_rfl
  rw [List.take_length] at hf
  exact hf

theorem prepared_build_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let code := PA17TableBuild005.buildProgram full.length q size
    CapacityThroughout q (PA17CellLayout003.capacityWords full.length q size) (givenTreeROM q full)
      code (initial (fun _ => 0)) ∧
      Invariant q full hq (execute (givenTreeROM q full).semantic code (initial (fun _ => 0))) := by
  intro size code
  let cap := PA17CellLayout003.capacityWords full.length q size
  let prepared := execute (givenTreeROM q full).semantic
    (PA17TablePrepare004.program full.length q size) (initial (fun _ => 0))
  have hi := prepared_prepare_invariant q full hq hlaminar
  have hs := schedule_capacityThroughout q cap full.length (givenTreeROM q full)
    (PA17TableBuild005.cellProgram full.length q size) (Invariant q full hq)
    (fun _ h => h.2.2) (by
      intro stage hstage budget hpos hb state hstate
      exact cell_step_safe q full hq hlaminar ⟨stage, hstage⟩ ⟨budget, hb⟩ hpos state hstate) prepared hi
  have hp := PA17TablePrepare004.prepared_program_capacityThroughout q full hq hlaminar (initial (fun _ => 0))
    (by intro address _; exact Nat.zero_le _)
  change CapacityThroughout q cap (givenTreeROM q full)
      (PA17TablePrepare004.program full.length q size ++
        PA17RowSchedule004.scheduleProgram (PA17TableBuild005.cellProgram full.length q size) full.length q)
      (initial (fun _ => 0)) ∧ _
  refine ⟨UniformFreeTableSafety.capacityThroughout_append q cap (givenTreeROM q full) _ _ (initial (fun _ => 0)) hp hs.2, ?_⟩
  change Invariant q full hq (execute (givenTreeROM q full).semantic
    (PA17TablePrepare004.program full.length q size ++
      PA17RowSchedule004.scheduleProgram (PA17TableBuild005.cellProgram full.length q size) full.length q) (initial (fun _ => 0)))
  rw [IndexedClosureRAM.execute_append]
  exact hs.1

theorem prepared_build_capacityThroughout (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    CapacityThroughout q (PA17CellLayout003.capacityWords full.length q size) (givenTreeROM q full)
      (PA17TableBuild005.buildProgram full.length q size) (initial (fun _ => 0)) :=
  (prepared_build_safe q full hq hlaminar).1

theorem prepared_build_physicalCardBounded (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    PhysicalCardBounded q full (execute (givenTreeROM q full).semantic
      (PA17TableBuild005.buildProgram full.length q size) (initial (fun _ => 0))).heap :=
  (prepared_build_safe q full hq hlaminar).2.2.1

end PaperProofs.Structure.LaminarTree.PA17BuildCapacity007
