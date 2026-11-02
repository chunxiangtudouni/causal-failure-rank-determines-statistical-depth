module

public import PaperProofs.Structure.UniformTreeMetadataRAM

/-! Runtime free-capacity slots copied from the actual metadata heap.
The combined phase computes its own cardinalities from givenTreeROM before
copying them. No cardinality or free vector is compiled into instructions. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.UniformFreeCapacityRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims

variable {Tool : Type*}

def freeProgram (size cardBase output : Nat) : List Op :=
  (IndexedCellRAM.copyWords cardBase output size).map Op.base ++
    (IndexedCellRAM.constantBlock (output + size) 1).map Op.base

def freeOutput (size metadataBase : Nat) : Nat := metadataBase + 3 * size + 1

def combinedProgram (N q size metadataBase : Nat) : List Op :=
  UniformTreeMetadataRAM.program N q size metadataBase ++
    freeProgram size metadataBase (freeOutput size metadataBase)

theorem freeProgram_tag (rom : ROM) (size cardBase output : Nat) (state : State) :
    (execute rom (freeProgram size cardBase output) state).heap (output + size) = 1 := by
  rw [freeProgram, IndexedClosureRAM.execute_append, execute_base, execute_base,
    IndexedCellRAM.execute_constantBlock_heap, Function.update_self]

theorem freeProgram_payload (rom : ROM) (size cardBase output : Nat)
    (hdisjoint : ∀ left < size, ∀ right < size, cardBase + left ≠ output + right)
    (state : State) (node : Nat) (hn : node < size) :
    (execute rom (freeProgram size cardBase output) state).heap (output + node) = state.heap (cardBase + node) := by
  rw [freeProgram, IndexedClosureRAM.execute_append, execute_base, execute_base,
    IndexedCellRAM.execute_constantBlock_heap, Function.update_of_ne (by omega),
    IndexedCellRAM.copyWords_value rom cardBase output size hdisjoint state node hn]

theorem freeProgram_result (cache : IndexedNodeCache Tool) (rom : ROM) (cardBase output : Nat)
    (hdisjoint : ∀ left < cache.nodes.size, ∀ right < cache.nodes.size, cardBase + left ≠ output + right)
    (state : State)
    (hcard : ∀ node : cache.NodeId, state.heap (cardBase + node.val) = (cache.decode node).card) :
    IndexedCellRAM.slot cache (execute rom (freeProgram cache.nodes.size cardBase output) state).heap output =
      IndexedEntry.free cache := by
  apply IndexedCellRAM.slot_eq_of_rep
  constructor
  · exact freeProgram_tag rom cache.nodes.size cardBase output state
  · intro node
    rw [freeProgram_payload rom cache.nodes.size cardBase output hdisjoint state node.val node.isLt,
      hcard node, IndexedEntry.reifyCapacity_get]

theorem freeProgram_frame (rom : ROM) (size cardBase output : Nat) (state : State) (address : Nat)
    (hframe : ∀ index ≤ size, address ≠ output + index) :
    (execute rom (freeProgram size cardBase output) state).heap address = state.heap address := by
  rw [freeProgram, IndexedClosureRAM.execute_append, execute_base, execute_base,
    IndexedCellRAM.execute_constantBlock_heap, Function.update_of_ne (hframe size le_rfl),
    IndexedCellRAM.copyWords_frame rom cardBase output size state address
      (fun index hi => hframe index (by omega))]

theorem freeProgram_length (size cardBase output : Nat) : (freeProgram size cardBase output).length = 4 * size + 3 := by
  have ht : (IndexedCellRAM.constantBlock (output + size) 1).length = 3 := rfl
  simp only [freeProgram, List.length_append, List.length_map, IndexedCellRAM.copyWords_length, ht]

theorem freeProgram_trace_length (size cardBase output : Nat) :
    (trace (freeProgram size cardBase output)).length = 38 * size + 27 := by
  have ht : (primitiveTrace (IndexedCellRAM.constantBlock (output + size) 1)).length = 27 := rfl
  rw [freeProgram, IndexedClosureRAM.trace_append, List.length_append, trace_base_length,
    trace_base_length, IndexedCellRAM.copyWords_trace_length, ht]

theorem combinedProgram_length (N q size metadataBase : Nat) :
    (combinedProgram N q size metadataBase).length = (3 * q + 18) * size + 6 := by
  rw [combinedProgram, List.length_append, UniformTreeMetadataRAM.program_length, freeProgram_length]
  simp only [Nat.add_mul]
  omega

theorem combinedProgram_trace_length (N q size metadataBase : Nat) :
    (trace (combinedProgram N q size metadataBase)).length = (30 * q + 169) * size + 54 := by
  rw [combinedProgram, IndexedClosureRAM.trace_append, List.length_append,
    UniformTreeMetadataRAM.program_trace_length, freeProgram_trace_length]
  simp only [Nat.add_mul]
  omega

theorem combinedProgram_codeWords_length (N q size metadataBase : Nat) :
    (haltingWords (combinedProgram N q size metadataBase)).length = (15 * q + 90) * size + 35 := by
  rw [IndexedClosureRAM.haltingWords, List.length_append, IndexedClosureRAM.programWords_length, combinedProgram_length]
  have hh : haltWords.toArray.toList.length = 5 := rfl
  rw [hh]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  omega

theorem combinedProgram_result (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (metadataBase : Nat) (state : State) :
    let cache := (prepareNormalization q full).indexed
    IndexedCellRAM.slot cache
      (execute (givenTreeROM q full).semantic (combinedProgram full.length q cache.nodes.size metadataBase) state).heap
      (freeOutput cache.nodes.size metadataBase) = IndexedEntry.free cache := by
  intro cache
  rw [combinedProgram, IndexedClosureRAM.execute_append]
  apply freeProgram_result cache (givenTreeROM q full).semantic metadataBase _
    (by intro left hl right hr; dsimp [freeOutput]; omega)
  intro node
  exact ((UniformTreeMetadataRAM.prepared_program_metadata q full hq hlaminar metadataBase state).2 node).1

theorem combinedProgram_preserves_metadata (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (metadataBase : Nat) (state : State) :
    UniformTreeMetadataRAM.MetadataCorrect q full metadataBase
      (execute (givenTreeROM q full).semantic
        (combinedProgram full.length q (prepareNormalization q full).indexed.nodes.size metadataBase) state).heap := by
  let size := (prepareNormalization q full).indexed.nodes.size
  let before := execute (givenTreeROM q full).semantic (UniformTreeMetadataRAM.program full.length q size metadataBase) state
  have hm : UniformTreeMetadataRAM.MetadataCorrect q full metadataBase before.heap :=
    UniformTreeMetadataRAM.prepared_program_metadata q full hq hlaminar metadataBase state
  have hframe (address : Nat) (ha : address ≤ metadataBase + 3 * size) :
      (execute (givenTreeROM q full).semantic (freeProgram size metadataBase (freeOutput size metadataBase)) before).heap address =
        before.heap address := freeProgram_frame _ _ _ _ _ address (by intro index hi; dsimp [freeOutput]; omega)
  rw [combinedProgram, IndexedClosureRAM.execute_append]
  constructor
  · rw [hframe _ (by dsimp [UniformTreeMetadataRAM.parentAddress]; omega)]
    exact hm.1
  · intro node
    rw [hframe _ (by dsimp [UniformTreeMetadataRAM.cardAddress]; have := node.isLt; omega),
      hframe _ (by dsimp [UniformTreeMetadataRAM.parentAddress]; have := node.isLt; omega),
      hframe _ (by dsimp [UniformTreeMetadataRAM.internalAddress]; have := node.isLt; omega)]
    exact hm.2 node

theorem combinedProgram_frame (rom : ROM) (N q size metadataBase : Nat) (state : State) (address : Nat)
    (hframe : address < metadataBase ∨ metadataBase + 4 * size + 1 < address) :
    (execute rom (combinedProgram N q size metadataBase) state).heap address = state.heap address := by
  rw [combinedProgram, IndexedClosureRAM.execute_append,
    freeProgram_frame rom size metadataBase (freeOutput size metadataBase) _ address
      (by intro index hi; dsimp [freeOutput]; omega)]
  exact UniformTreeMetadataRAM.program_frame rom N q size metadataBase state address (by omega)

theorem combinedProgram_halting_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (metadataBase : Nat) (state : State) (hpc : state.pc = 0) :
    let cache := (prepareNormalization q full).indexed
    ∃ final operations,
      HaltingRuns (givenTreeROM q full).semantic (combinedProgram full.length q cache.nodes.size metadataBase) state final operations ∧
      IndexedCellRAM.slot cache final.heap (freeOutput cache.nodes.size metadataBase) = IndexedEntry.free cache ∧
      UniformTreeMetadataRAM.MetadataCorrect q full metadataBase final.heap ∧
      (∀ address : Nat, address < metadataBase ∨ metadataBase + 4 * cache.nodes.size + 1 < address →
        final.heap address = state.heap address) ∧
      operations.length ≤ 229 * (q * cache.nodes.size + cache.nodes.size) := by
  intro cache
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < cache.nodes.size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  refine ⟨_, _, IndexedClosureRAM.execute_halts _ _ state hpc,
    combinedProgram_result q full hq hlaminar metadataBase state,
    combinedProgram_preserves_metadata q full hq hlaminar metadataBase state, ?_, ?_⟩
  · intro address hframe
    exact combinedProgram_frame _ _ _ _ _ state address hframe
  · rw [List.length_append, combinedProgram_trace_length, IndexedClosureRAM.haltTrace_length]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_add]
    omega

end PaperProofs.Structure.LaminarTree.UniformFreeCapacityRAM
