module

public import PaperProofs.Structure.PA17_TableCell_004
public import PaperProofs.Structure.PA17_TablePrepare_004
public import PaperProofs.Structure.PA17_RowSchedule_004

/-! Actual tag-first full table construction from the original given-tree
ROM and zero heap. Runtime metadata/stage matching and boundary initialization
feed concrete persistent-table cells in reverse-stage/positive-budget order.
The local schedule contract is discharged here, not an input assumption.
Finite-word, complete capacity-prefix and packing/code-generator claims remain
separate; this file asserts physical Nat-heap table correctness and real traces. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17TableBuild005

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001
open PA17RowSchedule004

def cellProgram (N q size stage budget : Nat) : List Op :=
  PA17TableCell004.program N q size (slot q (stage + 1) budget)
    (slot q (stage + 1) (budget - 1)) (slot q stage budget) stage

def buildProgram (N q size : Nat) : List Op :=
  PA17TablePrepare004.program N q size ++ scheduleProgram (cellProgram N q size) N q

def TagsBounded (q : Nat) (full : List (Finset (Fin q))) (heap : Nat → Nat) : Prop :=
  ∀ index < cells full.length q,
    heap (index * ((prepareNormalization q full).indexed.nodes.size + 1)) ≤ 1

def Invariant (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (state : State) : Prop :=
  PA17TableCell004.Persistent q full hq state.heap ∧ TagsBounded q full state.heap

theorem slot_bound (N q stage budget : Nat) (hstage : stage ≤ N) (hbudget : budget < q + 2) :
    slot q stage budget < cells N q := by
  have hh := Nat.mul_le_mul_right (q + 2) (show stage + 1 ≤ N + 1 by omega)
  rw [Nat.add_mul, Nat.one_mul] at hh
  dsimp [slot, cells]
  omega

theorem slots_ne_of_pair_ne (q leftStage leftBudget rightStage rightBudget : Nat)
    (hl : leftBudget < q + 2) (hr : rightBudget < q + 2)
    (hne : leftStage ≠ rightStage ∨ leftBudget ≠ rightBudget) :
    slot q leftStage leftBudget ≠ slot q rightStage rightBudget := by
  by_cases hs : leftStage = rightStage
  · have hb : leftBudget ≠ rightBudget := hne.resolve_left (not_not.mpr hs)
    dsimp [slot]
    rw [hs]
    intro he
    exact hb (Nat.add_left_cancel he)
  · simpa only [slot, PA17TerminalRow002.slotBase, Nat.add_assoc] using
      PA17TerminalRow002.slotBase_disjoint (q + 1) leftStage rightStage hs leftBudget rightBudget (by omega) (by omega)

theorem tag_le_one_of_rep {Tool : Type*} (cache : IndexedNodeCache Tool) (heap : Nat → Nat)
    (base : Nat) (entry : IndexedEntry.FixedEntry cache) (hrep : TagFirstRep cache heap base entry) :
    heap base ≤ 1 := by
  cases entry with
  | void => rw [hrep]; exact Nat.zero_le _
  | vector capacity => rw [hrep.1]

theorem singleCellContract (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    SingleCellContract q full (givenTreeROM q full).semantic
      (cellProgram full.length q (prepareNormalization q full).indexed.nodes.size) (Invariant q full hq) := by
  intro stage budget hbudget state hinvariant
  let cache := (prepareNormalization q full).indexed
  let size := cache.nodes.size
  let goodSlot := slot q (stage.val + 1) budget.val
  let badSlot := slot q (stage.val + 1) (budget.val - 1)
  let outputSlot := slot q stage.val budget.val
  have hgood : goodSlot < cells full.length q := slot_bound _ _ _ _ (by have := stage.isLt; omega) budget.isLt
  have hbad : badSlot < cells full.length q := slot_bound _ _ _ _ (by have := stage.isLt; omega) (by omega)
  have hout : outputSlot < cells full.length q := slot_bound _ _ _ _ (by have := stage.isLt; omega) budget.isLt
  let good := readEntry size goodSlot state.heap
  let bad := readEntry size badSlot state.heap
  have hg : TagFirstRep cache state.heap (PA17TableCell004.tableBase size goodSlot) good :=
    rep_of_readEntry cache goodSlot state.heap good (hinvariant.2 goodSlot hgood) rfl
  have hb : TagFirstRep cache state.heap (PA17TableCell004.tableBase size badSlot) bad :=
    rep_of_readEntry cache badSlot state.heap bad (hinvariant.2 badSlot hbad) rfl
  have ho := PA17TableCell004.prepared_program_output q full hq hlaminar goodSlot badSlot outputSlot
    hgood hbad hout stage good bad state hinvariant.1 hg hb
  have hp := PA17TableCell004.prepared_program_persistent q full hq hlaminar goodSlot badSlot outputSlot hout stage state hinvariant.1
  have htags : TagsBounded q full (execute (givenTreeROM q full).semantic
      (cellProgram full.length q size stage.val budget.val) state).heap := by
    intro other hs
    by_cases heq : other = outputSlot
    · subst other
      exact tag_le_one_of_rep cache _ _ _ ho
    · have hf := PA17TableCell004.prepared_program_frame q full hq hlaminar goodSlot badSlot outputSlot
        stage state hinvariant.1 (other * (size + 1))
        (Or.inl (by
          simpa only [Nat.add_zero] using PA17CellLayout003.table_slot_bound full.length q size other hs 0 (Nat.zero_le _)))
        (by
          intro index hi
          simpa only [PA17TableCell004.tableBase, Nat.add_zero] using
            PA17TableCell004.tableSlots_disjoint size other outputSlot heq 0 (Nat.zero_le _) index hi)
      change (execute (givenTreeROM q full).semantic
        (PA17TableCell004.program full.length q size goodSlot badSlot outputSlot stage.val) state).heap _ ≤ 1
      rw [hf]
      exact hinvariant.2 other hs
  refine ⟨⟨hp, htags⟩, ?_, ?_⟩
  · exact PA17TableCell004.prepared_program_readEntry q full hq hlaminar goodSlot badSlot outputSlot
      hgood hbad hout stage good bad state hinvariant.1 hg hb
  · intro otherStage otherBudget hne
    exact PA17TableCell004.prepared_program_readEntry_frame q full hq hlaminar goodSlot badSlot outputSlot stage state hinvariant.1
      (slot q otherStage.val otherBudget.val) (slot_bound _ _ _ _ (by have := otherStage.isLt; omega) otherBudget.isLt)
      (slots_ne_of_pair_ne q _ _ _ _ otherBudget.isLt budget.isLt hne)

theorem prepare_invariant (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    Invariant q full hq (execute (givenTreeROM q full).semantic
      (PA17TablePrepare004.program full.length q size) (initial (fun _ => 0))) := by
  intro size
  have hc := PA17TablePrepare004.prepared_program_correct q full hq hlaminar (initial (fun _ => 0))
  exact ⟨⟨hc.1, hc.2.1⟩, PA17TablePrepare004.prepared_program_tags q full hq hlaminar (initial (fun _ => 0))
    (by intro index _; exact Nat.zero_le _)⟩

theorem prepared_build_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let result := execute (givenTreeROM q full).semantic (buildProgram full.length q size) (initial (fun _ => 0))
    PhysicalTableCorrect q full result.heap ∧ PA17TableCell004.Persistent q full hq result.heap := by
  intro size result
  let prepared := execute (givenTreeROM q full).semantic
    (PA17TablePrepare004.program full.length q size) (initial (fun _ => 0))
  have hr := full_schedule_correct q full (givenTreeROM q full).semantic (cellProgram full.length q size)
    (Invariant q full hq) (singleCellContract q full hq hlaminar) prepared
    (prepare_invariant q full hq hlaminar)
    (PA17TablePrepare004.prepared_program_budgetZero q full hq hlaminar (initial (fun _ => 0)))
    (PA17TablePrepare004.prepared_program_terminal q full hq hlaminar (initial (fun _ => 0)))
  have heq : result = execute (givenTreeROM q full).semantic (scheduleProgram (cellProgram full.length q size) full.length q) prepared := by
    dsimp [result, buildProgram, prepared]
    rw [IndexedClosureRAM.execute_append]
  rw [heq]
  exact ⟨⟨hr.2.2, hr.1.2⟩, hr.1.1⟩

theorem buildProgram_trace_le (N q size : Nat) (hsize : 0 < size) :
    (trace (buildProgram N q size) ++ haltTrace).length ≤ 1170 * work N q size := by
  have hp := PA17TablePrepare004.program_trace_le N q size hsize
  have hc : ∀ stage < N, ∀ budget, 0 < budget → budget < q + 2 →
      (trace (cellProgram N q size stage budget)).length ≤ 710 * size := by
    intro stage _ budget _ _
    rw [cellProgram, PA17TableCell004.program_trace_length]
    omega
  have hs := scheduleProgram_trace_le (cellProgram N q size) N q (710 * size) hc
  have hm : N * ((q + 1) * size) ≤ (N + 1) * ((q + 1) * size) :=
    Nat.mul_le_mul_right ((q + 1) * size) (Nat.le_succ N)
  have hsw : (trace (scheduleProgram (cellProgram N q size) N q)).length ≤ 710 * work N q size := by
    dsimp [work]
    nlinarith
  rw [List.length_append, haltTrace_length] at hp
  rw [buildProgram, trace_append, List.length_append, List.length_append, haltTrace_length]
  omega

theorem prepared_build_halting (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ∃ final operations,
      HaltingRuns (givenTreeROM q full).semantic (buildProgram full.length q size)
        (initial (fun _ => 0)) final operations ∧
      PhysicalTableCorrect q full final.heap ∧
      PA17TableCell004.Persistent q full hq final.heap ∧
      operations.length ≤ 1170 * work full.length q size := by
  intro size
  have hc := prepared_build_correct q full hq hlaminar
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  exact ⟨_, _, execute_halts _ _ (initial (fun _ => 0)) rfl, hc.1, hc.2,
    buildProgram_trace_le full.length q size hsize⟩

end PaperProofs.Structure.LaminarTree.PA17TableBuild005
