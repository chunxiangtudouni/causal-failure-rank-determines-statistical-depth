module
public import PaperProofs.Structure.PA17_FullBuildWord_036a
public import PaperProofs.Structure.PA17_GivenWord_031e
public import PaperProofs.Structure.PA17_QueryWord_033

/-! Actual complete full-table builder numeric/access execution, using its
proved original zero-heap capacity invariant and freshly computed metadata. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17FullBuildWord036b

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022

theorem flatMap_numeric_invariant (B heapWords : Nat) (rom : PhysicalROM) (block : Nat → List Op)
    (invariant : State → Prop) (indices : List Nat)
    (hstep : ∀ index ∈ indices, ∀ state, invariant state → RegistersLE B state →
      invariant (execute rom.semantic (block index) state) ∧ NumericSafe B heapWords rom (block index) state)
    (state : State) (hi : invariant state) (hr : RegistersLE B state) :
    invariant (execute rom.semantic (indices.flatMap block) state) ∧
      NumericSafe B heapWords rom (indices.flatMap block) state := by
  induction indices generalizing state with
  | nil => exact ⟨hi, PA17GivenWord031a.NumericSafe.nil _ _ _ _ hr⟩
  | cons head later ih =>
    have hh := hstep head List.mem_cons_self state hi hr
    have ht := ih (fun index hm => hstep index (List.mem_cons_of_mem _ hm)) _ hh.1 (hh.2.final _ _ _ _ _)
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    exact ⟨ht.1, NumericSafe.append _ _ _ _ _ _ hh.2 ht.2⟩

theorem parentHeap_bound {Tool : Type*} (cache : IndexedNodeCache Tool) (parents : Nat) (heap : Nat → Nat)
    (hp : PA17HeapAncestors001.ParentHeapFor cache parents heap) :
    ∀ encoded ≤ cache.nodes.size, heap (parents + encoded) ≤ cache.nodes.size := by
  intro encoded he
  cases encoded with
  | zero => rw [Nat.add_zero, hp.1]; exact Nat.zero_le _
  | succ index =>
    let node : cache.NodeId := ⟨index, by omega⟩
    rw [hp.2 node]
    exact UniformNormalizationRAM.encodedNode_le cache _

theorem cell_layout (B N q size goodSlot stage : Nat)
    (hheap : PA17QueryLayout014.heapWords N q size ≤ B) (hq : q ≤ B) (hsize : 0 < size)
    (hgood : goodSlot < cells N q) (hs : stage < N) :
    PA17GivenWord031d.Layout B (PA17QueryLayout014.heapWords N q size) q
      (PA17CellLayout003.capacityWords N q size) size (PA17CellLayout003.workBase N q size)
      (goodSlot * (size + 1)) (PA17CellLayout003.accumulatorBase N q size)
      (PA17CellLayout003.metadataBase N q size + size) (PA17CellLayout003.stageBase N q size + stage) := by
  have hcap : PA17CellLayout003.capacityWords N q size ≤ PA17QueryLayout014.heapWords N q size := Nat.le_add_right _ _
  have hgoodWord := PA17CellLayout003.table_slot_bound N q size goodSlot hgood size le_rfl
  have hsizeHeap := (PA17QueryBudgetWord032.regions_fit N q size).2.2.2.2.2.1
  refine {
    cap_access := hcap, cap_bound := hcap.trans hheap, q_bound := hq,
    size_bound := by omega, size_pos := hsize,
    work_region := ?_, parent_access := ?_, parent_bound := ?_, stage_access := ?_, stage_bound := ?_,
    disjoint := PA17CellLayout003.work_parent_disjoint N q size,
    good_region := ?_, accumulator := ?_ }
  all_goals
    dsimp only [PA17CellLayout003.capacityWords, PA17CellLayout003.workBase,
      PA17CellLayout003.accumulatorBase, PA17CellLayout003.metadataBase, PA17CellLayout003.stageBase,
      PA17QueryLayout014.heapWords, PA17QueryLayout014.capacityWords, PA17QueryLayout014.indexWords] at *
    omega

theorem assembly_numeric (q : Nat) (full : List (Finset (Fin q))) (B : Nat)
    (hl : PA17QueryBudgetWord032.Layout B full.length q (prepareNormalization q full).indexed.nodes.size
      (queryROM q full 0 ∅)) (state : State) (hi : RegistersLE (2 * B) state) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (PA17QueryLayout014.heapWords full.length q size) (givenTreeROM q full)
      (PA17MetadataAssembly003.program full.length q size (PA17CellLayout003.capacityWords full.length q size)) state := by
  intro size
  have hmeta := (PA17QueryBudgetWord032.regions_fit full.length q size).1
  have hm := PA17FullBuildWord036a.given_metadata_numeric q full B _ _
    ⟨hl.input_bound, hmeta.trans hl.heap_bound, hmeta, hl.q_bound⟩ state hi
  have hstage : PA17MetadataAssembly003.stageBase size (PA17CellLayout003.capacityWords full.length q size) + full.length ≤
      PA17QueryLayout014.heapWords full.length q size := by
    dsimp [PA17MetadataAssembly003.stageBase, PA17QueryLayout014.heapWords, PA17QueryLayout014.indexWords,
      PA17QueryLayout014.capacityWords]
    omega
  have hinput : (givenTreeROM q full).input.length ≤ B := by
    have hh := hl.input_bound
    change ((givenTreeROM q full).input ++ [0] ++ _).length ≤ B at hh
    simp only [List.length_append, List.length_cons, List.length_nil] at hh
    omega
  have hone : 1 ≤ B := (PA17QueryBudgetWord032.regions_fit full.length q size).2.2.2.2.2.2.2.trans hl.heap_bound
  have hsize : size ≤ B := by have := hmeta.trans hl.heap_bound; omega
  rw [PA17MetadataAssembly003.program]
  exact NumericSafe.append _ _ _ _ _ state hm
    (PA17GivenWord031e.program_numeric B _ full.length q size _ (givenTreeROM q full)
      (PA17GivenWord031e.givenTreeROM_data q full) hinput hl.q_bound hsize hone hstage
      (hstage.trans hl.heap_bound) _ (hm.final _ _ _ _ _))

theorem freeSlot_numeric (q : Nat) (full : List (Finset (Fin q))) (B slot : Nat)
    (hheap : PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size ≤ B)
    (hq : q ≤ B) (hs : slot ∈ PA17TerminalRow002.seedSlots full.length q)
    (state : State) (hi : RegistersLE (2 * B) state)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full
      (PA17CellLayout003.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let cap := PA17CellLayout003.capacityWords full.length q size
    NumericSafe (2 * B) (PA17QueryLayout014.heapWords full.length q size) (givenTreeROM q full)
      (PA17TerminalRow002.writeFreeSlot size cap slot) state := by
  intro size cap
  have hsource : cap + size ≤ PA17QueryLayout014.heapWords full.length q size := by
    dsimp [cap, PA17QueryLayout014.heapWords, PA17QueryLayout014.indexWords, PA17QueryLayout014.capacityWords]
    omega
  have htarget := PA17TablePrepare004.seedSlots_bound full.length q size slot hs
  have hcap : cap ≤ PA17QueryLayout014.heapWords full.length q size := Nat.le_add_right _ _
  have hcopy := PA17GivenWord031a.copyWords_numeric B _ size cap (PA17TerminalRow002.slotBase size slot + 1)
    (givenTreeROM q full) hsource (hsource.trans hheap) (by dsimp [PA17TerminalRow002.slotBase]; nlinarith)
    (by dsimp [PA17TerminalRow002.slotBase]; nlinarith) state hi (by
      intro node hn
      exact (UniformTreeMetadataRAM.metadata_card_bound q full cap state.heap hm ⟨node, hn⟩).trans (by omega))
  rw [PA17TerminalRow002.writeFreeSlot]
  apply NumericSafe.append _ _ _ _ _ state hcopy
  apply PA17GivenWord031a.constantBlock_numeric B _ _ 1 (givenTreeROM q full)
    ⟨by dsimp [PA17TerminalRow002.slotBase]; nlinarith, by dsimp [PA17TerminalRow002.slotBase]; nlinarith⟩
    (by have := (PA17QueryBudgetWord032.regions_fit full.length q size).2.2.2.2.2.2.2.trans hheap; omega)
    _ (hcopy.final _ _ _ _ _)

theorem freeSlots_numeric (q : Nat) (full : List (Finset (Fin q))) (B : Nat)
    (hheap : PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size ≤ B)
    (hq : q ≤ B) (slots : List Nat) (hs : ∀ slot ∈ slots, slot ∈ PA17TerminalRow002.seedSlots full.length q)
    (state : State) (hi : RegistersLE (2 * B) state)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full
      (PA17CellLayout003.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let cap := PA17CellLayout003.capacityWords full.length q size
    NumericSafe (2 * B) (PA17QueryLayout014.heapWords full.length q size) (givenTreeROM q full)
      (PA17TerminalRow002.freeSlots size cap slots) state := by
  intro size cap
  induction slots generalizing state with
  | nil => exact PA17GivenWord031a.NumericSafe.nil _ _ _ _ hi
  | cons head later ih =>
    have hh := freeSlot_numeric q full B head hheap hq (hs head List.mem_cons_self) state hi hm
    rw [PA17TerminalRow002.freeSlots, List.flatMap_cons]
    apply NumericSafe.append _ _ _ _ _ state hh
    apply ih (fun slot hs' => hs slot (List.mem_cons_of_mem _ hs')) _ (hh.final _ _ _ _ _)
    apply PA17Rolling018.metadata_transfer q full cap state.heap _ hm
    intro address ha _
    exact PA17TerminalRow002.writeFreeSlot_frame _ size cap head state address (by
      intro offset ho
      have hb := PA17TablePrepare004.seedSlots_bound full.length q size head (hs head List.mem_cons_self)
      dsimp [PA17TerminalRow002.slotBase]
      nlinarith)

theorem prepare_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (B : Nat)
    (hl : PA17QueryBudgetWord032.Layout B full.length q (prepareNormalization q full).indexed.nodes.size
      (queryROM q full 0 ∅)) (state : State) (hi : RegistersLE (2 * B) state) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (PA17QueryLayout014.heapWords full.length q size) (givenTreeROM q full)
      (PA17TablePrepare004.program full.length q size) state := by
  intro size
  have hm := assembly_numeric q full B hl state hi
  rw [PA17TablePrepare004.program]
  exact NumericSafe.append _ _ _ _ _ state hm
    (freeSlots_numeric q full B hl.heap_bound hl.q_bound (PA17TerminalRow002.seedSlots full.length q)
      (fun _ hs => hs) _ (hm.final _ _ _ _ _)
      (PA17MetadataAssembly003.prepared_program_correct q full hq hlaminar _ state).1)

end PaperProofs.Structure.LaminarTree.PA17FullBuildWord036b
