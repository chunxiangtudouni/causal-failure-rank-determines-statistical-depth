module

public import Structure.PA06_A19Prepare_InitialUsed037_Run
public import Structure.PA06_A19Prepare_PreBuild044_Frames
public import Structure.PA06_A19Prepare_FinalRepresentation056_HeaderFrame

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED finite transport from the actual037 Current invariant.
No original caller table/metadata oracle or whole HeapRepresents premise is
introduced. Source semantic facts are consumed only by transfer lemmas. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalRepresentation057
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PreparePreBuild044 (bits capacity packedWords controlBase ScalarData)
open PA06A19PrepareInitialUsed037 (Current scalar)

theorem current_logical_table_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original after : WordState (bits q full))
    (current : Current q full used original q after)
    (address : Nat) (ha : address < tableWords full.length q (treeSize q full)) :
    logicalHeap q (capacity q full) after.heap address =
      logicalHeap q (capacity q full) original.heap address := by
  simpa only [logicalHeap, ite_eq_right (Nat.ne_of_gt hq), scalar] using current.table_frame address ha

theorem current_table_correct (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original after : WordState (bits q full))
    (current : Current q full used original q after)
    (table : PhysicalTableCorrect q full (logicalHeap q (capacity q full) original.heap)) :
    PhysicalTableCorrect q full (logicalHeap q (capacity q full) after.heap) := by
  apply (PA06A19PreparePackedView013.physicalTableCorrect_congr_prefix q full _ _ ?_).mpr table
  intro address ha
  apply current_logical_table_frame q full used hq original after current address
  simpa only [PA06A19PreparePreBuild044.prepared_size q full hq] using ha

theorem current_used_bits (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original after : WordState (bits q full))
    (current : Current q full used original q after) (tool : Fin q) :
    logicalHeap q (capacity q full) after.heap (tableWords full.length q (treeSize q full) + tool.val) =
      bit (decide (tool ∈ used)) := by
  simpa only [logicalHeap, ite_eq_right (Nat.ne_of_gt hq), scalar] using current.written tool tool.isLt

theorem current_logical_bounded (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original after : WordState (bits q full))
    (current : Current q full used original q after) :
    CapacityPrefixBounded q (capacity q full) (logicalHeap q (capacity q full) after.heap) := by
  simpa only [logicalHeap, ite_eq_right (Nat.ne_of_gt hq)] using current.bounded

/-- GLOBAL abstract-state address normalization for the existing finite
ordinary frame; each real control slot is fitted before comparing words. -/
theorem current_ordinary_at (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original after : WordState (bits q full))
    (current : Current q full used original q after)
    (hbase : (original.register .address).toNat = controlBase q full)
    (point : Nat) (hfit : Fits (bits q full) point) (hlow : 4 + packedWords q full ≤ point)
    (h16 : point ≠ controlBase q full + 16) (h17 : point ≠ controlBase q full + 17)
    (h18 : point ≠ controlBase q full + 18) :
    after.heap (BitVec.ofNat (bits q full) point) = original.heap (BitVec.ofNat (bits q full) point) := by
  have hCBfit : Fits (bits q full) (controlBase q full) := by
    simpa only [Nat.add_zero] using (PA06A19PrepareInitialUsed037.actual_control_room q full hq 0 (by decide)).2
  have hbaseWord : original.register .address = BitVec.ofNat (bits q full) (controlBase q full) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hCBfit]
    exact hbase
  have different (offset : Nat) (ho : offset ≤ 511) (hne : point ≠ controlBase q full + offset) :
      BitVec.ofNat (bits q full) point ≠ original.register .address + BitVec.ofNat (bits q full) offset := by
    intro he
    have hn := congrArg BitVec.toNat he
    have hf : Fits (bits q full) (controlBase q full + offset) :=
      (PA06A19PrepareInitialUsed037.actual_control_room q full hq offset ho).2
    simp only [hbaseWord, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hfit, Nat.mod_eq_of_lt hf] at hn
    exact hne hn
  apply current.ordinary_frame
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
    exact hlow
  · exact different 16 (by decide) h16
  · exact different 17 (by decide) h17
  · exact different 18 (by decide) h18

theorem current_bank_field_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original after : WordState (bits q full))
    (current : Current q full used original q after)
    (hbase : (original.register .address).toNat = controlBase q full)
    (offset : Nat) (ho : offset ≤ 6) :
    after.heap (BitVec.ofNat (bits q full) (controlBase q full + offset)) =
      original.heap (BitVec.ofNat (bits q full) (controlBase q full + offset)) := by
  have hfit : Fits (bits q full) (controlBase q full + offset) :=
    (PA06A19PrepareInitialUsed037.actual_control_room q full hq offset
      (ho.trans (by decide : 6 ≤ 511))).2
  have hlow : 4 + packedWords q full ≤ controlBase q full + offset :=
    (Nat.le_succ _).trans (PA06A19PrepareInitialUsed037.actual_control_after_lookahead q full offset)
  exact current_ordinary_at q full used hq original after current hbase
    (controlBase q full + offset) hfit hlow
    (ne_of_lt (Nat.add_lt_add_left (ho.trans_lt (by decide : 6 < 16)) (controlBase q full)))
    (ne_of_lt (Nat.add_lt_add_left (ho.trans_lt (by decide : 6 < 17)) (controlBase q full)))
    (ne_of_lt (Nat.add_lt_add_left (ho.trans_lt (by decide : 6 < 18)) (controlBase q full)))

theorem current_metadata_physical_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (original after : WordState (bits q full))
    (current : Current q full used original q after)
    (hbase : (original.register .address).toNat = controlBase q full)
    (position : Nat) (hp : position < (staticMetadata q full).length) :
    after.heap (BitVec.ofNat (bits q full) (6 + packedWords q full + position)) =
      original.heap (BitVec.ofNat (bits q full) (6 + packedWords q full + position)) := by
  have hP : PA06A19PrepareChildrenCache023.actualPackedWords q full = packedWords q full := by
    simp only [PA06A19PrepareChildrenCache023.actualPackedWords, packedWords, capacity, bits,
      PA06A19PreparePreBuild044.prepared_size q full hq]
  have bounds := PA06A19PrepareStaticMetadata036.actual_metadata_output_bounds q full hq hl
  have hEnd : 6 + packedWords q full + (staticMetadata q full).length ≤ controlBase q full := by
    simpa only [hP, PA06A19PreparePreBuild044.children_controlBase q full hq] using bounds.1
  have hfit : Fits (bits q full) (6 + packedWords q full + position) := by
    simpa only [hP] using (bounds.2.2 position hp).2
  have hbefore : 6 + packedWords q full + position < controlBase q full := by omega
  exact current_ordinary_at q full used hq original after current hbase _ hfit (by omega)
    (by omega) (by omega) (by omega)

theorem current_metadata_logical_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (original after : WordState (bits q full))
    (current : Current q full used original q after)
    (hbase : (original.register .address).toNat = controlBase q full)
    (position : Nat) (hp : position < (staticMetadata q full).length) :
    logicalHeap q (capacity q full) after.heap (capacity q full + 2 + position) =
      logicalHeap q (capacity q full) original.heap (capacity q full + 2 + position) := by
  rw [PA06A19PrepareFinalRepresentation056.logical_metadata_word q (capacity q full) position after.heap hq,
    PA06A19PrepareFinalRepresentation056.logical_metadata_word q (capacity q full) position original.heap hq]
  exact congrArg BitVec.toNat (current_metadata_physical_frame q full used hq hl original after current hbase position hp)

theorem current_scalarData (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (original after : WordState (bits q full))
    (current : Current q full used original q after) (data : ScalarData q full original) :
    ScalarData q full after := by
  apply PA06A19PreparePreBuild044.ScalarData.of_frame data current.base
  intro offset ho
  exact current_bank_field_frame q full used hq original after current data.bank037.base offset (by omega)

theorem scalarData_finalHeaderBank (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (bits q full)) (data : ScalarData q full state) :
    PA06A19PrepareFinalHeader033.BankData q full state :=
  ⟨data.bank037.base, data.bank037.T, data.bank037.C, data.bank032.P⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalRepresentation057
