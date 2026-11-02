module

public import Structure.PA06_A19Prepare_FinalRepresentation056_HeaderFrame
public import Structure.PA06_A19Prepare_PreBuild044_Frames

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED finite consequences of the actual532 MetadataAllowed
frame. Only existing data predicates are transported; no new representation
framework, caller hSafe or future metadata answer is introduced. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalRepresentation059
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PreparePreBuild044 (bits capacity packedWords controlBase ScalarData)
open PA06A19PrepareStaticMetadata036 (MetadataAllowed)
open PA06A19PrepareBankNodeBit022 (wordView)

theorem metadata_packed_words (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PrepareChildrenCache023.actualPackedWords q full = packedWords q full := by
  simp only [PA06A19PrepareChildrenCache023.actualPackedWords, packedWords, capacity, bits,
    PA06A19PreparePreBuild044.prepared_size q full hq]

theorem metadata_end_le_control (q : Nat) (full : List (Finset (Fin q))) :
    6 + packedWords q full + (6 * treeSize q full + full.length + q) ≤ controlBase q full :=
  PA06A19PrepareStaticMetadata036.metadata_output_end_le_control
    full.length q (treeSize q full) (packedWords q full)

theorem metadata_packed_end_le_control (q : Nat) (full : List (Finset (Fin q))) :
    4 + packedWords q full ≤ controlBase q full := by
  unfold controlBase PA06A19PrepareControlBank017.controlBase
  omega

/-- Actual staticMetadata addresses fit and its last real word is below
CB. Laminar is used only here for the original metadata-length identity. -/
theorem metadata_actual_address_bounds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (position : Nat) (hp : position < (staticMetadata q full).length) :
    6 + packedWords q full + position < controlBase q full ∧
      Fits (bits q full) (6 + packedWords q full + position) := by
  have bounds := PA06A19PrepareStaticMetadata036.actual_metadata_output_bounds q full hq hl
  have hP := metadata_packed_words q full hq
  have hEnd : 6 + packedWords q full + (staticMetadata q full).length ≤ controlBase q full := by
    simpa only [hP, PA06A19PreparePreBuild044.children_controlBase q full hq] using bounds.1
  exact ⟨by omega, by simpa only [hP] using (bounds.2.2 position hp).2⟩

/-- GLOBAL abstract-state finite packed-word proof. The actual physical
frame has no permission to write these packed words. -/
theorem metadata_logical_capacity_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : WordState (bits q full))
    (frame : ∀ point : BitVec (bits q full),
      ¬ MetadataAllowed q full (PA06A19PrepareChildrenCache023.actualControlBase q full)
        (PA06A19PrepareChildrenCache023.actualPackedWords q full) point.toNat →
      after.heap point = before.heap point) :
    ∀ address < capacity q full,
      logicalHeap q (capacity q full) after.heap address = logicalHeap q (capacity q full) before.heap address := by
  have hCBfit : Fits (bits q full) (controlBase q full) := by
    simpa only [Nat.add_zero] using PA06A19PrepareRuntimeLayout026.actual_bank_field_fits q full hq 0 (by decide)
  have packedEnd := metadata_packed_end_le_control q full
  have hP := metadata_packed_words q full hq
  intro address ha
  apply PA06A19PrepareFinalRepresentation056.logical_capacity_congr_words q (capacity q full) hq
    (PA17PackingBounds043.bits_pos full.length q) before.heap after.heap ?_ address ha
  intro point hlow hhigh
  change point < 4 + packedWords q full at hhigh
  have hf : Fits (bits q full) point := (by omega : point ≤ controlBase q full).trans_lt hCBfit
  apply frame
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
  simp only [MetadataAllowed, hP, PA06A19PreparePreBuild044.children_controlBase q full hq]
  dsimp only [controlBase, packedWords, capacity, bits] at packedEnd hhigh ⊢
  omega

theorem metadata_table_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : WordState (bits q full))
    (frame : ∀ point : BitVec (bits q full),
      ¬ MetadataAllowed q full (PA06A19PrepareChildrenCache023.actualControlBase q full)
        (PA06A19PrepareChildrenCache023.actualPackedWords q full) point.toNat →
      after.heap point = before.heap point)
    (table : PhysicalTableCorrect q full (logicalHeap q (capacity q full) before.heap)) :
    PhysicalTableCorrect q full (logicalHeap q (capacity q full) after.heap) := by
  apply (PA06A19PreparePackedView013.physicalTableCorrect_congr_prefix q full _ _ ?_).mpr table
  intro address ha
  apply metadata_logical_capacity_frame q full hq before after frame address
  have bound := PA06A19PreparePackedView013.oldCapacity_le_capacity full.length q (treeSize q full) hq
  have tableBound := PA06A19PreparePackedView013.tableWords_le_oldCapacity full.length q (treeSize q full)
  have ha' : address < tableWords full.length q (treeSize q full) := by
    simpa only [PA06A19PreparePreBuild044.prepared_size q full hq] using ha
  exact ha'.trans_le (tableBound.trans bound)

theorem metadata_logical_bounded (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : WordState (bits q full))
    (frame : ∀ point : BitVec (bits q full),
      ¬ MetadataAllowed q full (PA06A19PrepareChildrenCache023.actualControlBase q full)
        (PA06A19PrepareChildrenCache023.actualPackedWords q full) point.toNat →
      after.heap point = before.heap point)
    (bounded : CapacityPrefixBounded q (capacity q full) (logicalHeap q (capacity q full) before.heap)) :
    CapacityPrefixBounded q (capacity q full) (logicalHeap q (capacity q full) after.heap) := by
  intro address ha
  rw [metadata_logical_capacity_frame q full hq before after frame address ha]
  exact bounded address ha

theorem metadata_bank_field_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : WordState (bits q full))
    (frame : ∀ point : BitVec (bits q full),
      ¬ MetadataAllowed q full (PA06A19PrepareChildrenCache023.actualControlBase q full)
        (PA06A19PrepareChildrenCache023.actualPackedWords q full) point.toNat →
      after.heap point = before.heap point)
    (offset : Nat) (ho : offset ≤ 6) :
    after.heap (BitVec.ofNat (bits q full) (controlBase q full + offset)) =
      before.heap (BitVec.ofNat (bits q full) (controlBase q full + offset)) := by
  have hf := PA06A19PrepareRuntimeLayout026.actual_bank_field_fits q full hq offset ho
  have hP := metadata_packed_words q full hq
  have hsize := (PA06A19PreparePreBuild044.prepared_size q full hq).symm
  have hEnd := metadata_end_le_control q full
  apply frame
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
  simp only [MetadataAllowed, hP, PA06A19PreparePreBuild044.children_controlBase q full hq, hsize]
  dsimp only [controlBase, packedWords, capacity, bits] at hEnd ⊢
  omega

theorem metadata_scalarData (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : WordState (bits q full))
    (frame : ∀ point : BitVec (bits q full),
      ¬ MetadataAllowed q full (PA06A19PrepareChildrenCache023.actualControlBase q full)
        (PA06A19PrepareChildrenCache023.actualPackedWords q full) point.toNat →
      after.heap point = before.heap point)
    (address : after.register .address = before.register .address) (data : ScalarData q full before) :
    ScalarData q full after := by
  apply PA06A19PreparePreBuild044.ScalarData.of_frame data address
  intro offset ho
  exact metadata_bank_field_frame q full hq before after frame offset (by omega)

theorem metadata_header_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : WordState (bits q full))
    (frame : ∀ point : BitVec (bits q full),
      ¬ MetadataAllowed q full (PA06A19PrepareChildrenCache023.actualControlBase q full)
        (PA06A19PrepareChildrenCache023.actualPackedWords q full) point.toNat →
      after.heap point = before.heap point)
    (header : PA06A19PrepareRuntimePacked016.Header q before.heap) :
    PA06A19PrepareRuntimePacked016.Header q after.heap := by
  apply PA06A19PreparePreBuild044.header_of_frame header
  intro point hp
  have packedEnd := metadata_packed_end_le_control q full
  have hCBfit : Fits (bits q full) (controlBase q full) := by
    simpa only [Nat.add_zero] using PA06A19PrepareRuntimeLayout026.actual_bank_field_fits q full hq 0 (by decide)
  have hf : Fits (bits q full) point := (by omega : point ≤ controlBase q full).trans_lt hCBfit
  have hP := metadata_packed_words q full hq
  apply frame
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
  simp only [MetadataAllowed, hP, PA06A19PreparePreBuild044.children_controlBase q full hq]
  omega

/-- The premise is the real058 words result; the main actual wrapper
below obtains it by executing058, rather than asking the original caller. -/
theorem metadata_words_to_logical (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (state : WordState (bits q full))
    (words : ∀ position < (staticMetadata q full).length,
      (wordView state).heap (6 + PA06A19PrepareChildrenCache023.actualPackedWords q full + position) =
        (staticMetadata q full).getD position 0) :
    ∀ position (hp : position < (staticMetadata q full).length),
      logicalHeap q (capacity q full) state.heap (capacity q full + 2 + position) =
        (staticMetadata q full)[position]'hp := by
  intro position hp
  rw [PA06A19PrepareFinalRepresentation056.logical_metadata_word q (capacity q full) position state.heap hq]
  have written := words position hp
  change (state.heap (BitVec.ofNat (bits q full)
    (6 + PA06A19PrepareChildrenCache023.actualPackedWords q full + position))).toNat = _ at written
  rw [metadata_packed_words q full hq, List.getD_eq_getElem _ 0 hp] at written
  exact written

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalRepresentation059
