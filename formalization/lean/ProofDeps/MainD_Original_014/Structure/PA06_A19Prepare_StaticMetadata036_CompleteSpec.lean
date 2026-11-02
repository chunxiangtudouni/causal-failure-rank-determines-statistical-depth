module

public import Structure.PA06_A19Prepare_StaticMetadata036_StageRun

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! One exact nine-segment output specification and original same-allocation
length/room. This states no constructor existence: actual running producers
must deliver every conjunct before the full metadata claim is counted. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass)

theorem metadata_length_exact (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full) :
    (staticMetadata q full).length = 6 * preparedSize q full + full.length + q := by
  rw [PSTRStaticLayout.metadata_length q full hq, PSTRStaticLayout.edgeCount_eq q full hq hl]
  change 1 + 5 * preparedSize q full + (preparedSize q full - 1) + full.length + q =
    6 * preparedSize q full + full.length + q
  have ht : 0 < preparedSize q full := by
    have h := PA06A19PrepareControlBank017.treeSize_pos full hq
    simpa only [treeSize, Nat.ne_of_gt hq, ite_false] using h
  omega

theorem metadata_output_end_le_control (N q t P : Nat) :
    6 + P + (6 * t + N + q) ≤ PA06A19PrepareControlBank017.controlBase N q t P := by
  unfold PA06A19PrepareControlBank017.controlBase PA06A19PrepareControlBank017.dimensions
    PA06A19PrepareControlBank017.mass
  omega

def fieldSegment : Field → Nat
  | .cardinality => 4 | .internal => 5 | .leaf => 6 | .stage => 7 | .tool => 8

private theorem fieldSegment_lt_chunks (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (field : Field) : fieldSegment field < (PSTRStaticLayout.chunks q full hq).length := by
  change fieldSegment field < 9
  cases field <;> decide

theorem field_address_original_offset (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (P : Nat) (field : Field) (index : Nat) :
    fieldAddress P full.length (preparedSize q full) field index =
      6 + P + PSTRStaticLayout.offset q full (fieldSegment field) + index := by
  have hedge := PSTRStaticLayout.edgeCount_eq q full hq hl
  have ht : 0 < preparedSize q full := by
    have h := PA06A19PrepareControlBank017.treeSize_pos full hq
    simpa only [treeSize, Nat.ne_of_gt hq, ite_false] using h
  have hsize : (prepareNormalization q full).indexed.nodes.size = preparedSize q full := rfl
  cases field <;>
    simp only [fieldAddress, fieldFactor, fieldExtra, fieldSegment, PSTRStaticLayout.offset, hedge, hsize] <;> omega

/-- Every original segment has a single source and the same indexed cache.
This is a concrete semantic proposition, not a set of accepted theorem
assumptions renamed as the desired full preprocessor conclusion. -/
def CompleteMetadataWritten (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (P : Nat) (state : NatState) : Prop :=
  AdjacencyWritten q full P state ∧
  (∀ node : (prepareNormalization q full).indexed.NodeId,
    state.heap (fieldAddress P full.length (preparedSize q full) .cardinality node.val) =
      (prepareNormalization q full).indexed.metadata.cardinalities.get node) ∧
  (∀ node : (prepareNormalization q full).indexed.NodeId,
    state.heap (fieldAddress P full.length (preparedSize q full) .internal node.val) =
      bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) ∧
  (∀ node : (prepareNormalization q full).indexed.NodeId,
    state.heap (fieldAddress P full.length (preparedSize q full) .leaf node.val) = originalLeaf q full node) ∧
  (∀ stage : Fin full.length,
    state.heap (fieldAddress P full.length (preparedSize q full) .stage stage.val) =
      encodedNode (prepareNormalization q full).indexed ((IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage)) ∧
  (∀ tool : Fin q,
    state.heap (fieldAddress P full.length (preparedSize q full) .tool tool.val) =
      ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool).val + 1)

/-- Explicit point correspondence to original chunks4..8. This transports
semantic values; it does not supply them to any actual machine program. -/
theorem complete_metadata_field_chunk (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (P : Nat) (state : NatState) (written : CompleteMetadataWritten q full hq P state)
    (field : Field) (index : Nat)
    (hi : index < ((PSTRStaticLayout.chunks q full hq)[fieldSegment field]'(by exact fieldSegment_lt_chunks q full hq field)).length) :
    state.heap (fieldAddress P full.length (preparedSize q full) field index) =
      ((PSTRStaticLayout.chunks q full hq)[fieldSegment field]'(by exact fieldSegment_lt_chunks q full hq field))[index]'hi := by
  cases field with
  | cardinality =>
    have hb : index < preparedSize q full := by simpa only [fieldSegment, PSTRStaticLayout.chunks,
      List.getElem_cons_succ, List.getElem_cons_zero, List.length_map, List.length_finRange] using hi
    have h := written.2.1 ⟨index, hb⟩
    simpa only [fieldSegment, PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
      List.getElem_map, List.getElem_finRange, Fin.cast_mk] using h
  | internal =>
    have hb : index < preparedSize q full := by simpa only [fieldSegment, PSTRStaticLayout.chunks,
      List.getElem_cons_succ, List.getElem_cons_zero, List.length_map, List.length_finRange] using hi
    have h := written.2.2.1 ⟨index, hb⟩
    simpa only [fieldSegment, PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
      List.getElem_map, List.getElem_finRange, Fin.cast_mk] using h
  | leaf =>
    have hb : index < preparedSize q full := by simpa only [fieldSegment, PSTRStaticLayout.chunks,
      List.getElem_cons_succ, List.getElem_cons_zero, List.length_map, List.length_finRange] using hi
    have h := written.2.2.2.1 ⟨index, hb⟩
    have hget := PSTRStaticLayout.mapped_finRange_get (originalLeaf q full)
      (⟨index, hb⟩ : (prepareNormalization q full).indexed.NodeId)
    change state.heap (fieldAddress P full.length (preparedSize q full) .leaf index) =
      ((List.finRange ((prepareNormalization q full).indexed.nodes.size)).map
        (originalLeaf q full))[index]'(by
          simpa only [List.length_map, List.length_finRange] using hb)
    exact h.trans hget.symm
  | stage =>
    have hb : index < full.length := by simpa only [fieldSegment, PSTRStaticLayout.chunks,
      List.getElem_cons_succ, List.getElem_cons_zero, List.length_map, List.length_finRange] using hi
    have h := written.2.2.2.2.1 ⟨index, hb⟩
    simpa only [fieldSegment, PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
      List.getElem_map, List.getElem_finRange, Fin.cast_mk] using h
  | tool =>
    have hb : index < q := by simpa only [fieldSegment, PSTRStaticLayout.chunks,
      List.getElem_cons_succ, List.getElem_cons_zero, List.length_map, List.length_finRange] using hi
    have h := written.2.2.2.2.2 ⟨index, hb⟩
    simpa only [fieldSegment, PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
      List.getElem_map, List.getElem_finRange, Fin.cast_mk] using h

/-- All nine segments imply the exact frozen staticMetadata at every
position. Conditional assembly is explicitly kept separate from a run. -/
theorem complete_metadata_original (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (P : Nat) (state : NatState) (written : CompleteMetadataWritten q full hq P state) :
    ∀ position < (staticMetadata q full).length,
      state.heap (6 + P + position) = (staticMetadata q full).getD position 0 := by
  intro position hp
  have ht : 0 < preparedSize q full := by
    have h := PA06A19PrepareControlBank017.treeSize_pos full hq
    simpa only [treeSize, Nat.ne_of_gt hq, ite_false] using h
  have hlen := metadata_length_exact q full hq hl
  have hsize : (prepareNormalization q full).indexed.nodes.size = preparedSize q full := rfl
  rw [hlen] at hp
  by_cases hadj : position < 3 * preparedSize q full
  · exact adjacencyWritten_static q full hq hl P state written.1 position hadj
  · have field : ∃ field : Field, ∃ index : Nat,
        index < ((PSTRStaticLayout.chunks q full hq)[fieldSegment field]'(by exact fieldSegment_lt_chunks q full hq field)).length ∧
          PSTRStaticLayout.offset q full (fieldSegment field) + index = position := by
      have hedge := PSTRStaticLayout.edgeCount_eq q full hq hl
      by_cases hc : position < 4 * preparedSize q full
      · refine ⟨.cardinality, position - 3 * preparedSize q full, ?_, ?_⟩ <;>
          simp only [fieldSegment, PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
            List.length_map, List.length_finRange, PSTRStaticLayout.offset, hedge, hsize] <;> omega
      · by_cases hi : position < 5 * preparedSize q full
        · refine ⟨.internal, position - 4 * preparedSize q full, ?_, ?_⟩ <;>
            simp only [fieldSegment, PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
              List.length_map, List.length_finRange, PSTRStaticLayout.offset, hedge, hsize] <;> omega
        · by_cases hl' : position < 6 * preparedSize q full
          · refine ⟨.leaf, position - 5 * preparedSize q full, ?_, ?_⟩ <;>
              simp only [fieldSegment, PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
                List.length_map, List.length_finRange, PSTRStaticLayout.offset, hedge, hsize] <;> omega
          · by_cases hs : position < 6 * preparedSize q full + full.length
            · refine ⟨.stage, position - 6 * preparedSize q full, ?_, ?_⟩ <;>
                simp only [fieldSegment, PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
                  List.length_map, List.length_finRange, PSTRStaticLayout.offset, hedge, hsize] <;> omega
            · refine ⟨.tool, position - (6 * preparedSize q full + full.length), ?_, ?_⟩ <;>
                simp only [fieldSegment, PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
                  List.length_map, List.length_finRange, PSTRStaticLayout.offset, hedge, hsize] <;> omega
    obtain ⟨field, index, hi, hoff⟩ := field
    have hword := complete_metadata_field_chunk q full hq P state written field index hi
    have hget := PSTRStaticLayout.metadata_chunk_getD q full hq (fieldSegment field) index
      (by cases field <;> decide) hi
    have haddress := field_address_original_offset q full hq hl P field index
    rw [hoff] at hget
    have had : fieldAddress P full.length (preparedSize q full) field index = 6 + P + position := by
      rw [haddress]
      omega
    rw [had] at hword
    exact hword.trans hget.symm

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
