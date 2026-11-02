module

public import PaperProofs.Structure.UniformFreeCapacityRAM

/-! The runtime free-capacity phase in A17's actual tag-first table layout.
Capacities occupy the leading size+1 words; metadata is built after them.
This avoids silently identifying the older tag-last work slot with readEntry.
Uniform code generation and full finite-word execution remain separate. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.UniformFreeTableRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims

variable {Tool : Type*}

def freeProgram (size cardBase : Nat) : List Op :=
  (IndexedCellRAM.copyWords cardBase 1 size).map Op.base ++
    (IndexedCellRAM.constantBlock 0 1).map Op.base

def program (N q size : Nat) : List Op :=
  UniformTreeMetadataRAM.program N q size (size + 1) ++ freeProgram size (size + 1)

theorem freeProgram_tag (rom : ROM) (size cardBase : Nat) (state : State) :
    (execute rom (freeProgram size cardBase) state).heap 0 = 1 := by
  rw [freeProgram, IndexedClosureRAM.execute_append, execute_base, execute_base,
    IndexedCellRAM.execute_constantBlock_heap, Function.update_self]

theorem freeProgram_payload (rom : ROM) (size cardBase : Nat)
    (hdisjoint : ∀ left < size, ∀ right < size, cardBase + left ≠ 1 + right)
    (state : State) (node : Nat) (hn : node < size) :
    (execute rom (freeProgram size cardBase) state).heap (1 + node) = state.heap (cardBase + node) := by
  rw [freeProgram, IndexedClosureRAM.execute_append, execute_base, execute_base,
    IndexedCellRAM.execute_constantBlock_heap, Function.update_of_ne (by omega),
    IndexedCellRAM.copyWords_value rom cardBase 1 size hdisjoint state node hn]

theorem freeProgram_frame (rom : ROM) (size cardBase : Nat) (state : State) (address : Nat)
    (hframe : size < address) :
    (execute rom (freeProgram size cardBase) state).heap address = state.heap address := by
  rw [freeProgram, IndexedClosureRAM.execute_append, execute_base, execute_base,
    IndexedCellRAM.execute_constantBlock_heap, Function.update_of_ne (by omega),
    IndexedCellRAM.copyWords_frame rom cardBase 1 size state address (by intro index hi; omega)]

theorem freeProgram_readEntry (cache : IndexedNodeCache Tool) (rom : ROM) (cardBase : Nat)
    (hdisjoint : ∀ left < cache.nodes.size, ∀ right < cache.nodes.size, cardBase + left ≠ 1 + right)
    (state : State) (hcard : ∀ node : cache.NodeId,
      state.heap (cardBase + node.val) = (cache.decode node).card) :
    readEntry cache.nodes.size 0 (execute rom (freeProgram cache.nodes.size cardBase) state).heap =
      IndexedEntry.free cache := by
  simp only [readEntry, Nat.zero_mul, freeProgram_tag, Nat.one_ne_zero, ite_false,
    Nat.zero_add, IndexedEntry.free]
  apply congrArg CapacityBits.Entry.vector
  apply Vector.ext
  intro index hindex
  change (Vector.ofFn _).get ⟨index, hindex⟩ =
    (IndexedEntry.reifyCapacity cache Finset.card).get ⟨index, hindex⟩
  rw [cache_get_ofFn, IndexedEntry.reifyCapacity_get,
    freeProgram_payload rom cache.nodes.size cardBase hdisjoint state index hindex]
  exact hcard ⟨index, hindex⟩

theorem prepared_program_result (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (state : State) :
    let cache := (prepareNormalization q full).indexed
    readEntry cache.nodes.size 0
      (execute (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state).heap =
      IndexedEntry.free cache := by
  intro cache
  rw [program, IndexedClosureRAM.execute_append]
  apply freeProgram_readEntry cache (givenTreeROM q full).semantic (cache.nodes.size + 1)
    (by intro left hl right hr; omega)
  intro node
  exact ((UniformTreeMetadataRAM.prepared_program_metadata q full hq hlaminar (cache.nodes.size + 1) state).2 node).1

theorem prepared_program_metadata (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (state : State) :
    let size := (prepareNormalization q full).indexed.nodes.size
    UniformTreeMetadataRAM.MetadataCorrect q full (size + 1)
      (execute (givenTreeROM q full).semantic (program full.length q size) state).heap := by
  intro size
  let before := execute (givenTreeROM q full).semantic
    (UniformTreeMetadataRAM.program full.length q size (size + 1)) state
  have hm := UniformTreeMetadataRAM.prepared_program_metadata q full hq hlaminar (size + 1) state
  rw [program, IndexedClosureRAM.execute_append]
  constructor
  · rw [freeProgram_frame _ _ _ _ _ (by dsimp [UniformTreeMetadataRAM.parentAddress]; omega)]
    exact hm.1
  · intro node
    rw [freeProgram_frame _ _ _ _ _ (by dsimp [UniformTreeMetadataRAM.cardAddress]; omega),
      freeProgram_frame _ _ _ _ _ (by dsimp [UniformTreeMetadataRAM.parentAddress]; omega),
      freeProgram_frame _ _ _ _ _ (by dsimp [UniformTreeMetadataRAM.internalAddress]; omega)]
    exact hm.2 node

theorem program_frame (rom : ROM) (N q size : Nat) (state : State) (address : Nat)
    (hframe : 4 * size + 1 < address) :
    (execute rom (program N q size) state).heap address = state.heap address := by
  rw [program, IndexedClosureRAM.execute_append,
    freeProgram_frame rom size (size + 1) _ address (by omega)]
  exact UniformTreeMetadataRAM.program_frame rom N q size (size + 1) state address (by omega)

theorem freeProgram_trace_length (size cardBase : Nat) :
    (trace (freeProgram size cardBase)).length = 38 * size + 27 := by
  rw [freeProgram, IndexedClosureRAM.trace_append, List.length_append,
    trace_base_length, trace_base_length, IndexedCellRAM.copyWords_trace_length]
  rfl

theorem program_trace_length (N q size : Nat) :
    (trace (program N q size)).length = (30 * q + 169) * size + 54 := by
  rw [program, IndexedClosureRAM.trace_append, List.length_append,
    UniformTreeMetadataRAM.program_trace_length, freeProgram_trace_length]
  ring

theorem prepared_halting_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (state : State) (hpc : state.pc = 0) :
    let cache := (prepareNormalization q full).indexed
    ∃ final operations,
      HaltingRuns (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state final operations ∧
      readEntry cache.nodes.size 0 final.heap = IndexedEntry.free cache ∧
      UniformTreeMetadataRAM.MetadataCorrect q full (cache.nodes.size + 1) final.heap ∧
      (∀ address, 4 * cache.nodes.size + 1 < address → final.heap address = state.heap address) ∧
      operations.length ≤ 229 * (q * cache.nodes.size + cache.nodes.size) := by
  intro cache
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < cache.nodes.size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  refine ⟨_, _, IndexedClosureRAM.execute_halts _ _ state hpc,
    prepared_program_result q full hq hlaminar state,
    prepared_program_metadata q full hq hlaminar state, ?_, ?_⟩
  · intro address ha
    exact program_frame _ _ _ _ _ address ha
  · rw [List.length_append, program_trace_length, haltTrace_length]
    simp only [Nat.add_mul, Nat.mul_assoc]
    have hqt : cache.nodes.size ≤ q * cache.nodes.size := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right cache.nodes.size (show 1 ≤ q from hq)
    omega

end PaperProofs.Structure.LaminarTree.UniformFreeTableRAM
