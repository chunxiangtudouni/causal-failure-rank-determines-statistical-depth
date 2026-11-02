module

public import PaperProofs.Structure.RawTreeSerialization

/-! The exact original serialized prefix containing its three region
lengths and the complete input region.  These are layout identities only;
no runtime writes or constructor are supplied by this module. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputLayout

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims RawTreeSerialization

def prefixWords (q : Nat) (full : List (Finset (Fin q))) : List Nat :=
  let size := (prepareNormalization q full).indexed.nodes.size
  [3 + full.length * q + size * q, 2 * size, size - 1, full.length, q, size] ++
    incidence full ++ incidence (prepareNormalization q full).indexed.nodes.toList

def prefixLength (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  6 + full.length * q + (prepareNormalization q full).indexed.nodes.size * q

theorem prefixWords_length (q : Nat) (full : List (Finset (Fin q))) :
    (prefixWords q full).length = prefixLength q full := by
  simp only [prefixWords, prefixLength, List.length_append, List.length_cons, List.length_nil,
    RawIncidenceLaminarRAM.incidence_length, Array.length_toList]

private theorem serializeROM_take_input (rom : PhysicalROM) :
    (serializeROM rom).take (3 + rom.input.length) =
      [rom.input.length, rom.internal.length, rom.children.length] ++ rom.input := by
  have hserialize : serializeROM rom =
      ([rom.input.length, rom.internal.length, rom.children.length] ++ rom.input) ++
        (rom.internal ++ rom.children) := by simp only [serializeROM, List.append_assoc]
  rw [hserialize]
  apply List.take_left'
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem prefixWords_eq_serialize_take (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    prefixWords q full = (serializeROM (givenTreeROM q full)).take (prefixLength q full) := by
  have hlength : prefixLength q full = 3 + (givenTreeROM q full).input.length := by
    rw [givenTreeROM_input_length]
    unfold prefixLength
    omega
  rw [hlength, serializeROM_take_input, givenTreeROM_input_length, givenTreeROM_internal_length,
    givenTreeROM_children_length q full hq hlaminar]
  simp only [givenTreeROM, UniformTreeMetadataRAM.nodeRows_eq_incidence, prefixWords,
    List.cons_append, List.nil_append]

/-- All six header positions, without any raw-input qualification. -/
theorem prefixWords_getD_header (q : Nat) (full : List (Finset (Fin q))) (position : Nat)
    (hposition : position < 6) :
    (prefixWords q full).getD position 0 =
      [3 + full.length * q + (prepareNormalization q full).indexed.nodes.size * q,
        2 * (prepareNormalization q full).indexed.nodes.size,
        (prepareNormalization q full).indexed.nodes.size - 1,
        full.length, q, (prepareNormalization q full).indexed.nodes.size].getD position 0 := by
  unfold prefixWords
  rw [List.getD_append _ _ _ _ (by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega), List.getD_append _ _ _ _ (by simpa using hposition)]

theorem prefixWords_getD_raw (q : Nat) (full : List (Finset (Fin q))) (position : Nat)
    (hposition : position < full.length * q) :
    (prefixWords q full).getD (6 + position) 0 = (incidence full).getD position 0 := by
  unfold prefixWords
  rw [List.getD_append _ _ _ _ (by
    simp only [List.length_append, List.length_cons, List.length_nil, RawIncidenceLaminarRAM.incidence_length]
    omega), List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]

theorem prefixWords_getD_node (q : Nat) (full : List (Finset (Fin q))) (position : Nat) :
    (prefixWords q full).getD (6 + full.length * q + position) 0 =
      (incidence (prepareNormalization q full).indexed.nodes.toList).getD position 0 := by
  unfold prefixWords
  rw [List.getD_append_right _ _ _ _ (by
    simp only [List.length_append, List.length_cons, List.length_nil, RawIncidenceLaminarRAM.incidence_length]
    omega)]
  simp only [List.length_append, List.length_cons, List.length_nil,
    RawIncidenceLaminarRAM.incidence_length, Nat.add_sub_cancel_left]

theorem prefixWords_getD_raw_bit (q : Nat) (full : List (Finset (Fin q)))
    (row : Fin full.length) (tool : Fin q) :
    (prefixWords q full).getD (6 + row.val * q + tool.val) 0 =
      bit (decide (tool ∈ full[row.val])) := by
  have hrow := Nat.mul_le_mul_right q (Nat.succ_le_of_lt row.isLt)
  rw [Nat.succ_mul] at hrow
  rw [show 6 + row.val * q + tool.val = 6 + (row.val * q + tool.val) by omega,
    prefixWords_getD_raw q full _ (by have := tool.isLt; omega),
    RawIncidenceLaminarRAM.incidence_getD q full row.val row.isLt tool]

theorem prefixWords_getD_node_bit (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) :
    (prefixWords q full).getD (6 + full.length * q + node.val * q + tool.val) 0 =
      bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) := by
  rw [show 6 + full.length * q + node.val * q + tool.val =
      6 + full.length * q + (node.val * q + tool.val) by omega,
    prefixWords_getD_node,
    RawIncidenceLaminarRAM.incidence_getD q (prepareNormalization q full).indexed.nodes.toList node.val
      (by simpa only [Array.length_toList] using node.isLt) tool]
  rfl

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputLayout
