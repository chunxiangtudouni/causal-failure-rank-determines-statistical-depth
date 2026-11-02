module

public import PaperProofs.Structure.RawTreePreprocessingClaims
public import PaperProofs.Structure.UniformTreeMetadataRAM
public import PaperProofs.Structure.PackingWordBounds
import Mathlib.Tactic.Linarith

/-! Exact output layout of the raw constructor.  These lemmas derive the
decoder clause from actual word-by-word heap contents; they do not provide
those contents or a constructor program.  All regions keep their original
order, including the original child-ID order. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawTreeSerialization

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims

theorem serializeROM_length (rom : PhysicalROM) :
    (serializeROM rom).length = 3 + rom.size := by
  simp only [serializeROM, PhysicalROM.size, List.length_append, List.length_cons, List.length_nil]
  omega

theorem givenTreeROM_input_length (q : Nat) (full : List (Finset (Fin q))) :
    (givenTreeROM q full).input.length =
      3 + full.length * q + (prepareNormalization q full).indexed.nodes.size * q := by
  simp only [givenTreeROM, List.length_append, List.length_cons, List.length_nil,
    UniformTreeMetadataRAM.nodeRows_eq_incidence, RawIncidenceLaminarRAM.incidence_length,
    Array.length_toList]

theorem givenTreeROM_internal_length (q : Nat) (full : List (Finset (Fin q))) :
    (givenTreeROM q full).internal.length = 2 * (prepareNormalization q full).indexed.nodes.size := by
  simp only [givenTreeROM, List.length_append, List.length_map, List.length_finRange]
  omega

theorem givenTreeROM_children_length (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (givenTreeROM q full).children.length = (prepareNormalization q full).indexed.nodes.size - 1 := by
  simp only [givenTreeROM, List.length_flatMap, List.length_map, Array.length_toList]
  rw [childArray_sum_finRange, prepared_indexed_edge_count q full hq hlaminar]

theorem serialize_givenTreeROM_length (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (serializeROM (givenTreeROM q full)).length =
      6 + full.length * q + (prepareNormalization q full).indexed.nodes.size * q +
        2 * (prepareNormalization q full).indexed.nodes.size +
          ((prepareNormalization q full).indexed.nodes.size - 1) := by
  rw [serializeROM_length]
  simp only [PhysicalROM.size, givenTreeROM_input_length, givenTreeROM_internal_length,
    givenTreeROM_children_length q full hq hlaminar]
  omega

theorem serialize_givenTreeROM_length_le (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (serializeROM (givenTreeROM q full)).length ≤ 8 * (full.length + q + 1) * q := by
  rw [serialize_givenTreeROM_length q full hq hlaminar]
  let t := (prepareNormalization q full).indexed.nodes.size
  have ht : t ≤ full.length + q + 1 := prepared_indexed_size_le q full
  have htq := Nat.mul_le_mul_right q ht
  have hNq : full.length * q ≤ (full.length + q + 1) * q :=
    Nat.mul_le_mul_right q (by omega)
  have ht3 : 3 * t ≤ 3 * (t * q) := by nlinarith
  have hM : 2 ≤ (full.length + q + 1) * q := by nlinarith
  have hsub : t - 1 ≤ t := Nat.sub_le _ _
  change 6 + full.length * q + t * q + 2 * t + (t - 1) ≤ _
  nlinarith

theorem serialize_givenTreeROM_length_fits (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    Fits (indexWidth 16 full.length q) (serializeROM (givenTreeROM q full)).length := by
  apply fits_indexWidth_of_lt_power
  have hlen := serialize_givenTreeROM_length_le q full hq hlaminar
  let base := full.length + q + 2
  have hbase : 2 ≤ base := by dsimp [base]; omega
  have hsize : (full.length + q + 1) * q ≤ base ^ 2 := by dsimp [base]; nlinarith
  have hpos : 0 < base ^ 2 := pow_pos (by omega) _
  have hpower : 16384 ≤ base ^ 14 := Nat.pow_le_pow_left hbase 14
  calc
    _ ≤ 8 * base ^ 2 := hlen.trans (by nlinarith)
    _ < base ^ 2 * 16384 := by nlinarith
    _ ≤ base ^ 2 * base ^ 14 := Nat.mul_le_mul_left _ hpower
    _ = base ^ 16 := by rw [← pow_add]

theorem serializeROM_getD_input (rom : PhysicalROM) (position : Nat)
    (hposition : position < rom.input.length) :
    (serializeROM rom).getD (3 + position) 0 = rom.input[position] := by
  simp only [serializeROM, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil]
  rw [Nat.add_sub_cancel_left, List.getD_append _ _ _ _ hposition,
    List.getD_eq_getElem _ 0 hposition]

theorem serializeROM_getD_internal (rom : PhysicalROM) (position : Nat)
    (hposition : position < rom.internal.length) :
    (serializeROM rom).getD (3 + rom.input.length + position) 0 = rom.internal[position] := by
  simp only [serializeROM, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_cons, List.length_nil]
  have hoff : 3 + rom.input.length + position - 3 = rom.input.length + position := by omega
  rw [hoff, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hposition, List.getD_eq_getElem _ 0 hposition]

theorem serializeROM_getD_children (rom : PhysicalROM) (position : Nat)
    (hposition : position < rom.children.length) :
    (serializeROM rom).getD (3 + rom.input.length + rom.internal.length + position) 0 =
      rom.children[position] := by
  simp only [serializeROM, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_cons, List.length_nil]
  have hoff : 3 + rom.input.length + rom.internal.length + position - 3 =
      rom.input.length + (rom.internal.length + position) := by omega
  rw [hoff, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ 0 hposition]

theorem readSerializedROM_of_words {bits : Nat} (rom : PhysicalROM)
    (heap : BitVec bits → BitVec bits)
    (hwords : ∀ position (hposition : position < (serializeROM rom).length),
      (heap (BitVec.ofNat bits position)).toNat = (serializeROM rom)[position]) :
    readSerializedROM heap = rom := by
  have hlen := serializeROM_length rom
  have h0 : (heap (BitVec.ofNat bits 0)).toNat = rom.input.length := by
    simpa only [serializeROM, List.cons_append, List.getElem_cons_zero] using hwords 0 (by omega)
  have h1 : (heap (BitVec.ofNat bits 1)).toNat = rom.internal.length := by
    simpa only [serializeROM, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] using
      hwords 1 (by omega)
  have h2 : (heap (BitVec.ofNat bits 2)).toNat = rom.children.length := by
    simpa only [serializeROM, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] using
      hwords 2 (by omega)
  have hin : heapWordsAt heap 3 rom.input.length = rom.input := by
    apply List.ext_getElem
    · simp only [heapWordsAt, List.length_map, List.length_range]
    · intro index hleft hright
      simp only [heapWordsAt, List.getElem_map, List.getElem_range]
      have hp : 3 + index < (serializeROM rom).length := by
        rw [hlen, PhysicalROM.size]; omega
      rw [hwords (3 + index) hp, ← List.getD_eq_getElem _ 0 hp,
        serializeROM_getD_input rom index hright]
  have hint : heapWordsAt heap (3 + rom.input.length) rom.internal.length = rom.internal := by
    apply List.ext_getElem
    · simp only [heapWordsAt, List.length_map, List.length_range]
    · intro index hleft hright
      simp only [heapWordsAt, List.getElem_map, List.getElem_range]
      have hp : 3 + rom.input.length + index < (serializeROM rom).length := by
        rw [hlen, PhysicalROM.size]; omega
      rw [hwords _ hp, ← List.getD_eq_getElem _ 0 hp,
        serializeROM_getD_internal rom index hright]
  have hchild : heapWordsAt heap (3 + rom.input.length + rom.internal.length) rom.children.length =
      rom.children := by
    apply List.ext_getElem
    · simp only [heapWordsAt, List.length_map, List.length_range]
    · intro index hleft hright
      simp only [heapWordsAt, List.getElem_map, List.getElem_range]
      have hp : 3 + rom.input.length + rom.internal.length + index < (serializeROM rom).length := by
        rw [hlen, PhysicalROM.size]; omega
      rw [hwords _ hp, ← List.getD_eq_getElem _ 0 hp,
        serializeROM_getD_children rom index hright]
  simp only [readSerializedROM, h0, h1, h2, hin, hint, hchild]

theorem treeOutputCorrect_of_words {bits : Nat} (q : Nat) (full : List (Finset (Fin q)))
    (heapWords : Nat) (result : WordState bits)
    (hsize : (result.register .old).toNat = (prepareNormalization q full).indexed.nodes.size)
    (hlength : (result.register .fresh).toNat = (serializeROM (givenTreeROM q full)).length)
    (hspace : (serializeROM (givenTreeROM q full)).length ≤ heapWords)
    (hwords : ∀ position (hposition : position < (serializeROM (givenTreeROM q full)).length),
      (result.heap (BitVec.ofNat bits position)).toNat = (serializeROM (givenTreeROM q full))[position]) :
    TreeOutputCorrect q full heapWords result := by
  exact ⟨hsize, hlength, hspace, hwords,
    readSerializedROM_of_words (givenTreeROM q full) result.heap hwords, prepared_indexed_size_le q full⟩

end PaperProofs.Structure.LaminarTree.RawTreeSerialization
