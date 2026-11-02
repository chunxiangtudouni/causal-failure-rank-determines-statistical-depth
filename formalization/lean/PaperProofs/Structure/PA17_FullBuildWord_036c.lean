module
public import PaperProofs.Structure.PA17_FullBuildWord_036b

/-! Actual zero-heap full build, all actual prefixes and original finite-word
execution, with no local correctness or safety oracle supplied by the caller. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17FullBuildWord036c

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022 PA17FullBuildWord036b

theorem cell_step_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (B : Nat)
    (hl : PA17QueryBudgetWord032.Layout B full.length q (prepareNormalization q full).indexed.nodes.size
      (queryROM q full 0 ∅)) (stage : Fin full.length) (budget : Fin (q + 2)) (hbudget : 0 < budget.val)
    (state : State) (hi : PA17BuildCapacity007.Invariant q full hq state) (hr : RegistersLE (2 * B) state) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let code := PA17TableBuild005.cellProgram full.length q size stage.val budget.val
    PA17BuildCapacity007.Invariant q full hq (execute (givenTreeROM q full).semantic code state) ∧
      NumericSafe (2 * B) (PA17QueryLayout014.heapWords full.length q size) (givenTreeROM q full) code state := by
  intro size code
  let goodSlot := PA17RowSchedule004.slot q (stage.val + 1) budget.val
  let badSlot := PA17RowSchedule004.slot q (stage.val + 1) (budget.val - 1)
  let outputSlot := PA17RowSchedule004.slot q stage.val budget.val
  have hgood : goodSlot < cells full.length q := PA17TableBuild005.slot_bound _ _ _ _ (by have := stage.isLt; omega) budget.isLt
  have hbad : badSlot < cells full.length q := PA17TableBuild005.slot_bound _ _ _ _ (by have := stage.isLt; omega) (by have := budget.isLt; omega)
  have hout : outputSlot < cells full.length q := PA17TableBuild005.slot_bound _ _ _ _ (by have := stage.isLt; omega) budget.isLt
  have hsafe := PA17BuildCapacity007.cell_step_safe q full hq hlaminar stage budget hbudget state hi
  have hparents := PA17HeapAncestors001.metadata_parentHeapFor q full _ state.heap hi.1.1.1
  have hparentBound := parentHeap_bound (prepareNormalization q full).indexed _ state.heap hparents
  have hstage : state.heap (PA17CellLayout003.stageBase full.length q size + stage.val) ≤ size :=
    (hi.1.1.2 stage).trans_le (UniformNormalizationRAM.encodedNode_le _ _)
  have hcell := cell_layout B full.length q size goodSlot stage.val hl.heap_bound hl.q_bound
    (PA17Implementation030.node_size_pos q full) hgood stage.isLt
  have htable := PA17CellLayout003.table_le_capacityWords full.length q size
  have hbadWord := PA17CellLayout003.table_slot_bound full.length q size badSlot hbad size le_rfl
  have houtWord := PA17CellLayout003.table_slot_bound full.length q size outputSlot hout size le_rfl
  refine ⟨hsafe.1, ?_⟩
  exact PA17GivenWord031d.cell_numeric_of_capacity B _ q _ size _ _ _ _ _ _ _ (givenTreeROM q full) hcell
    (PA17GivenWord031b.givenTreeROM_internalData q full) (hbadWord.trans_le htable) (houtWord.trans_le htable)
    (by
      intro left hl right hr
      exact Ne.symm (PA17CellLayout003.work_good_disjoint full.length q size badSlot hbad right hr left hl))
    (PA17CellLayout003.work_good_disjoint full.length q size outputSlot hout)
    (by dsimp [PA17CellLayout003.metadataBase]; omega)
    (by dsimp [PA17CellLayout003.stageBase, PA17CellLayout003.metadataBase]; omega)
    state hr hstage hparentBound hsafe.2

theorem row_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (B : Nat)
    (hl : PA17QueryBudgetWord032.Layout B full.length q (prepareNormalization q full).indexed.nodes.size
      (queryROM q full 0 ∅)) (stage : Fin full.length)
    (state : State) (hi : PA17BuildCapacity007.Invariant q full hq state) (hr : RegistersLE (2 * B) state) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let code := PA17RowSchedule004.rowProgram (PA17TableBuild005.cellProgram full.length q size) q stage.val
    PA17BuildCapacity007.Invariant q full hq (execute (givenTreeROM q full).semantic code state) ∧
      NumericSafe (2 * B) (PA17QueryLayout014.heapWords full.length q size) (givenTreeROM q full) code state := by
  intro size code
  apply flatMap_numeric_invariant
  · intro budget hb before hbefore hregister
    have hh := (PA17RowSchedule004.positiveBudgets_mem q budget).mp hb
    exact cell_step_numeric q full hq hlaminar B hl stage ⟨budget, hh.2⟩ hh.1 before hbefore hregister
  · exact hi
  · exact hr

theorem schedule_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (B : Nat)
    (hl : PA17QueryBudgetWord032.Layout B full.length q (prepareNormalization q full).indexed.nodes.size
      (queryROM q full 0 ∅))
    (state : State) (hi : PA17BuildCapacity007.Invariant q full hq state) (hr : RegistersLE (2 * B) state) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let code := PA17RowSchedule004.scheduleProgram (PA17TableBuild005.cellProgram full.length q size) full.length q
    PA17BuildCapacity007.Invariant q full hq (execute (givenTreeROM q full).semantic code state) ∧
      NumericSafe (2 * B) (PA17QueryLayout014.heapWords full.length q size) (givenTreeROM q full) code state := by
  intro size code
  apply flatMap_numeric_invariant
  · intro stage hs before hbefore hregister
    have hh := List.mem_range.mp (List.mem_reverse.mp hs)
    exact row_numeric q full hq hlaminar B hl ⟨stage, hh⟩ before hbefore hregister
  · exact hi
  · exact hr

theorem prepared_program_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (65536 * (full.length + q + 2) ^ 3) (PA17QueryLayout014.heapWords full.length q size)
      (givenTreeROM q full) (PA17TableBuild005.buildProgram full.length q size) (initial (fun _ => 0)) := by
  intro size
  let B := PA17QueryBudgetWord032.bound full.length q
  have hl := PA17QueryBudgetWord032.prepared_layout q full 0 ∅
  have hp := prepare_numeric q full hq hlaminar B hl (initial (fun _ => 0)) (by intro register; exact Nat.zero_le _)
  have hs := schedule_numeric q full hq hlaminar B hl _
    (PA17BuildCapacity007.prepared_prepare_invariant q full hq hlaminar) (hp.final _ _ _ _ _)
  rw [← PA17QueryBudgetWord032.twice_bound]
  rw [PA17TableBuild005.buildProgram]
  exact NumericSafe.append _ _ _ _ _ _ hp hs.2

theorem work_le_cube (N q size : Nat) (hsize : size ≤ N + q + 1) :
    work N q size ≤ (N + q + 2) ^ 3 := by
  have hN : N + 1 ≤ N + q + 2 := by omega
  have hq : q + 1 ≤ N + q + 2 := by omega
  have ht : size ≤ N + q + 2 := by omega
  calc
    _ ≤ ((N + q + 2) * (N + q + 2)) * (N + q + 2) := Nat.mul_le_mul (Nat.mul_le_mul hN hq) ht
    _ = _ := by ring

theorem prepared_footprint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    (givenTreeROM q full).size + PA17QueryLayout014.heapWords full.length q size +
      (haltingWords (PA17TableBuild005.buildProgram full.length q size)).length ≤ 65536 * (full.length + q + 2) ^ 3 := by
  intro size
  have hc := PA17Implementation030.prepared_build_totalCost q full hq hlaminar
  have hw := work_le_cube full.length q size (prepared_indexed_size_le q full)
  change totalBuildCost (givenTreeROM q full) (PA17TableBuild005.buildProgram full.length q size)
    (PA17QueryLayout014.heapWords full.length q size) ≤ 32768 * work full.length q size at hc
  unfold totalBuildCost at hc
  nlinarith

theorem prepared_executionClaims (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ExecutionClaims 32 full.length q (PA17QueryLayout014.heapWords full.length q size) (givenTreeROM q full)
      (PA17TableBuild005.buildProgram full.length q size) (initial (fun _ => 0)) := by
  intro size
  have hn := prepared_program_numeric q full hq hlaminar
  exact PA17WordBounds023.executionClaims_of_numeric_prefix full.length q _ _ _ (initial (fun _ => 0)) rfl
    (PA17WordBounds023.givenTreeROM_wordsFit q full) (prepared_footprint q full hq hlaminar)
    (by intro address _; exact pow_pos (by decide) _) hn.1 hn.2

end PaperProofs.Structure.LaminarTree.PA17FullBuildWord036c
