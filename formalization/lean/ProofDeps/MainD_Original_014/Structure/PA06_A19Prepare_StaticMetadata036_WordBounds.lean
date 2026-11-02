module

public import Structure.PA06_A19Prepare_StaticMetadata036_MetadataRun
public import Structure.PA06_A19Prepare_BankPacked021_Prefix
public import Structure.PA06_A19Prepare_ChildrenCache023_WordBounds

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Original-width bounds for all nine metadata fields and all actual
ordinary/control addresses. Root's frozen021 control factory and017 same
8192 allocation are reused; no extra caller room or Fit16 condition is added.
This is numeric preparation, NOT the missing all-prefix execution proof. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass actualPackedWords actualControlBase actualAllocation mass_fits32)

theorem metadata_word_le_mass (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (value : Nat) (hv : value ∈ staticMetadata q full) : value ≤ mass q full := by
  have ht : preparedSize q full ≤ mass q full := prepared_indexed_size_le q full
  rw [PSTRStaticLayout.metadata_chunks q full hq] at hv
  obtain ⟨words, hw, hv⟩ := List.mem_flatten.mp hv
  simp only [PSTRStaticLayout.chunks, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [List.mem_singleton] at hv
    subst value
    rw [PSTRStaticLayout.edgeCount_eq q full hq hl]
    change preparedSize q full - 1 ≤ mass q full
    omega
  · obtain ⟨node, _hn, rfl⟩ := List.mem_map.mp hv
    exact (UniformNormalizationRAM.encodedNode_le _ _).trans ht
  · obtain ⟨node, _hn, rfl⟩ := List.mem_map.mp hv
    exact (RawTreeOutputWords.prepared_child_size_le q full node).trans ht
  · exact RawTreeOutputWords.givenTreeROM_word_le q full .children value hv
  · obtain ⟨node, _hn, rfl⟩ := List.mem_map.mp hv
    have hc := metadata_cardinality_le_q q (prepareNormalization q full).indexed node
    unfold mass
    omega
  · obtain ⟨node, _hn, rfl⟩ := List.mem_map.mp hv
    cases h : (prepareNormalization q full).indexed.metadata.isInternal.get node <;> simp [bit]
  · obtain ⟨node, _hn, rfl⟩ := List.mem_map.mp hv
    cases h : (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
    | none => simp only; omega
    | some tool => simp only; have hb := tool.isLt; unfold mass; omega
  · obtain ⟨stage, _hs, rfl⟩ := List.mem_map.mp hv
    exact (UniformNormalizationRAM.encodedNode_le _ _).trans ht
  · obtain ⟨tool, _ht, rfl⟩ := List.mem_map.mp hv
    have hb : ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool).val < preparedSize q full :=
      ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool).isLt
    omega

theorem metadata_wordsFit32 (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full) :
    WordsFit (indexWidth 32 full.length q) (staticMetadata q full) := by
  intro value hv
  exact (metadata_word_le_mass q full hq hl value hv).trans_lt (mass_fits32 q full)

/-- Every named producer cell is in the SAME original allocation and width.
The concrete source is the frozen021 root_control_room/fits factory. -/
theorem actual_metadata_control_slot (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (slot : Nat) (hs : slot ≤ 511) :
    actualControlBase q full + slot < actualAllocation q full ∧
      Fits (indexWidth 32 full.length q) (actualControlBase q full + slot) := by
  let C := capacityWords 8192 full.length q (preparedSize q full)
  have hf : Fits (indexWidth 32 full.length q)
      (4 + packedCapacityWords q C (indexWidth 32 full.length q) +
        8192 * (full.length + q + preparedSize q full + 1)) := by
    have h := PA06A19PrepareControlBank017.actual_allocation_fits full
    simpa only [C, treeSize, Nat.ne_of_gt hq, ite_false, PA06A19PrepareControlBank017.allocation,
      PA06A19PrepareControlBank017.dimensions, PA06A19PrepareControlBank017.mass,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have room := PA06A19PrepareBankPacked021.root_control_room full.length q (preparedSize q full) C slot hs
  have fit := PA06A19PrepareBankPacked021.root_control_fits full.length q (preparedSize q full) C slot hs hf
  constructor
  · simpa only [actualControlBase, actualPackedWords, actualAllocation, C,
      PA06A19PrepareControlBank017.controlBase, PA06A19PrepareControlBank017.allocation,
      PA06A19PrepareControlBank017.dimensions, PA06A19PrepareControlBank017.mass,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using room
  · simpa only [actualControlBase, actualPackedWords, C,
      PA06A19PrepareControlBank017.controlBase, PA06A19PrepareControlBank017.dimensions,
      PA06A19PrepareControlBank017.mass, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using fit

/-- The complete original metadata end is before the actual CB and every
actual output address fits; no expanded heap eligibility is required. -/
theorem actual_metadata_output_bounds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full) :
    6 + actualPackedWords q full + (staticMetadata q full).length ≤ actualControlBase q full ∧
    Fits (indexWidth 32 full.length q) (6 + actualPackedWords q full + (staticMetadata q full).length) ∧
    ∀ position < (staticMetadata q full).length,
      6 + actualPackedWords q full + position < actualAllocation q full ∧
      Fits (indexWidth 32 full.length q) (6 + actualPackedWords q full + position) := by
  have endLe : 6 + actualPackedWords q full + (staticMetadata q full).length ≤ actualControlBase q full := by
    rw [metadata_length_exact q full hq hl]
    exact metadata_output_end_le_control full.length q (preparedSize q full) (actualPackedWords q full)
  have control := actual_metadata_control_slot q full hq 0 (by decide)
  simp only [Nat.add_zero] at control
  refine ⟨endLe, endLe.trans_lt control.2, ?_⟩
  intro position hp
  have ha : 6 + actualPackedWords q full + position < actualControlBase q full := by omega
  exact ⟨ha.trans control.1, ha.trans control.2⟩

/-- Finite values and addresses convert the actual Nat output cells to their
physical word representation. All-prefix execution remains a separate proof. -/
theorem metadata_output_toWord (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (state : NatState)
    (written : ∀ position < (staticMetadata q full).length,
      state.heap (6 + actualPackedWords q full + position) = (staticMetadata q full).getD position 0) :
    ∀ position < (staticMetadata q full).length,
      (PA06A19PrepareBankNodeBit022.wordView (state.toWord (indexWidth 32 full.length q))).heap
        (6 + actualPackedWords q full + position) = (staticMetadata q full).getD position 0 := by
  intro position hp
  have ha := (actual_metadata_output_bounds q full hq hl).2.2 position hp
  have hv : Fits (indexWidth 32 full.length q) (state.heap (6 + actualPackedWords q full + position)) := by
    rw [written position hp, List.getD_eq_getElem _ 0 hp]
    exact metadata_wordsFit32 q full hq hl _ (List.getElem_mem hp)
  simp only [PA06A19PrepareBankNodeBit022.wordView, NatState.toWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha.2, Nat.mod_eq_of_lt hv]
  exact written position hp

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
