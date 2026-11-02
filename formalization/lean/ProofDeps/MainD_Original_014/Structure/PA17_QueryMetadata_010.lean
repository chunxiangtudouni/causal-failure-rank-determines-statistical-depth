module

public import Structure.PA17_QueryCounts_008
public import PaperProofs.Structure.UniformFreeTableSafety

/-! Recompute query metadata from the real query ROM. The caller's arbitrary
correct table heap is not assumed to contain correct metadata. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryMetadata010

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def program (N q size base : Nat) : List Op := UniformTreeMetadataRAM.program N q size base

theorem queryROM_internal_read (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (used : Finset (Fin q)) (address : Nat) :
    (queryROM q full stage used).semantic.read .internal address =
      (givenTreeROM q full).semantic.read .internal address := rfl

theorem queryROM_children_read (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (used : Finset (Fin q)) (address : Nat) :
    (queryROM q full stage used).semantic.read .children address =
      (givenTreeROM q full).semantic.read .children address := rfl

theorem rowSum_eq_card (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (used : Finset (Fin q)) (node : (prepareNormalization q full).indexed.NodeId) :
    UniformTreeMetadataRAM.rowSum (queryROM q full stage used).semantic full.length q node.val =
      ((prepareNormalization q full).indexed.decode node).card := by
  rw [UniformTreeMetadataRAM.rowSum]
  have heq : (List.range q).map (fun tool => (queryROM q full stage used).semantic.read .input
      (3 + full.length * q + node.val * q + tool)) =
      (List.finRange q).map (fun tool => bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node))) := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_finRange]
    · intro index hi _
      have hindex : index < q := by simpa only [List.length_map, List.length_range] using hi
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
      exact PA17QueryCounts008.queryROM_node_bit q full stage used node ⟨index, hindex⟩
  rw [heq, UniformTreeMetadataRAM.bit_row_card]

theorem prepared_program_metadata (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (stage : Nat) (used : Finset (Fin q))
    (base : Nat) (state : State) :
    UniformTreeMetadataRAM.MetadataCorrect q full base
      (execute (queryROM q full stage used).semantic
        (program full.length q (prepareNormalization q full).indexed.nodes.size base) state).heap := by
  constructor
  · exact UniformTreeMetadataRAM.program_parent_zero _ _ _ _ _ state
  · intro node
    have hqv := UniformTreeMetadataRAM.program_values (queryROM q full stage used).semantic
      full.length q (prepareNormalization q full).indexed.nodes.size base state node.val node.isLt
    have hgv := UniformTreeMetadataRAM.prepared_program_values q full hq hlaminar base state node
    have hrv := UniformTreeMetadataRAM.program_values (givenTreeROM q full).semantic
      full.length q (prepareNormalization q full).indexed.nodes.size base state node.val node.isLt
    refine ⟨hqv.1.trans (rowSum_eq_card q full stage used node), ?_, ?_⟩
    · exact hqv.2.1.trans (hrv.2.1.symm.trans hgv.2.1)
    · exact hqv.2.2.trans (hrv.2.2.symm.trans hgv.2.2)

theorem program_take_frame (rom : ROM) (N q size base count : Nat) (state : State)
    (address : Nat) (ha : address < base) :
    (execute rom ((program N q size base).take count) state).heap address = state.heap address := by
  by_cases hc : count ≤ (program N q size base).length
  · exact UniformFreeTableSafety.metadataProgram_prefixFrame rom N q size base address ha state count hc
  · rw [List.take_of_length_le (by omega)]
    exact UniformTreeMetadataRAM.program_frame rom N q size base state address (Or.inl ha)

theorem program_capacityThroughout (rom : PhysicalROM) (N q size base capWords : Nat)
    (hbase : capWords ≤ base) (state : State) (hcapacity : CapacityPrefixBounded q capWords state.heap) :
    CapacityThroughout q capWords rom (program N q size base) state :=
  UniformFreeTableSafety.metadataProgram_capacityThroughout q capWords rom N q size base hbase state hcapacity

theorem program_trace_length (N q size base : Nat) :
    (trace (program N q size base)).length = (30 * q + 131) * size + 27 :=
  UniformTreeMetadataRAM.program_trace_length N q size base

theorem totalQueryCost_le (N q size base : Nat) (hsize : 0 < size) :
    totalQueryCost q (program N q size base) ≤ 400 * queryWork q size := by
  rw [totalQueryCost, program, UniformTreeMetadataRAM.program_codeWords_length,
    List.length_append, UniformTreeMetadataRAM.program_trace_length, haltTrace_length]
  dsimp [queryWork]
  nlinarith

end PaperProofs.Structure.LaminarTree.PA17QueryMetadata010
