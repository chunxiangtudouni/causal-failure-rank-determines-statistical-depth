module

public import Structure.PA06_A19Prepare_ChildrenCache023_Invariants
public import PaperProofs.Structure.PA17_WordBounds_023

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled numeric preparation for the children-cache Word port.
This file proves data/counter/output room only. It does not claim all-clock
Word safety before the Nat producer and its nine real blocks are validated. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateChildrenLayout RawCandidateChildrenPrefix

theorem preparedSize_le_mass (q : Nat) (full : List (Finset (Fin q))) : preparedSize q full ≤ mass q full :=
  prepared_indexed_size_le q full

theorem parentWord_le (q : Nat) (full : List (Finset (Fin q))) (child : Nat) (hc : child < preparedSize q full) :
    parentWord q full child ≤ preparedSize q full := by
  rw [parentWord, givenTreeROM_parentWords q full child hc]
  exact UniformNormalizationRAM.encodedNode_le _ _

theorem input_parent_le (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (state : NatState)
    (input : InputData q full CB state) (child : Nat) (hc : child < preparedSize q full) :
    state.heap (parentAddress CB (mass q full) child) ≤ preparedSize q full := by
  rw [input.parents child hc]
  exact parentWord_le q full child hc

theorem beforeList_length_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (parent : Nat) (hp : parent ≤ preparedSize q full) :
    (beforeList q full parent).length ≤ preparedSize q full - 1 := by
  have h := flatPrefix_length_mono (preparedSize q full) (parentWord q full) parent (preparedSize q full) hp
  rw [flatPrefix_full, (exact_lists q full hq hl).2.2] at h
  exact h

theorem rowList_length_le (q : Nat) (full : List (Finset (Fin q))) (parent child : Nat)
    (hc : child ≤ preparedSize q full) : (rowList q full parent child).length ≤ preparedSize q full :=
  (childPrefix_length_le_upto (preparedSize q full) (parentWord q full) parent child).trans hc

theorem scanList_length_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (parent child : Nat) (hp : parent < preparedSize q full) (hc : child ≤ preparedSize q full) :
    (scanList q full parent child).length ≤ preparedSize q full - 1 := by
  have h := partial_span_le_total (preparedSize q full) (parentWord q full) parent child hp hc
  rw [(exact_lists q full hq hl).2.2] at h
  simpa only [scanList, beforeList, rowList, List.length_append] using h

theorem outer_ready_bounds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (CB parent pointer : Nat) (state : NatState) (ready : OuterReady q full CB parent pointer state)
    (hp : parent ≤ preparedSize q full) :
    state.heap (CB + 64) ≤ preparedSize q full ∧ state.heap (CB + 66) ≤ preparedSize q full - 1 := by
  rw [ready.parent_cell, ready.flat_cell]
  exact ⟨hp, beforeList_length_le q full hq hl parent hp⟩

theorem inner_ready_bounds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (CB parent child pointer : Nat) (state : NatState) (ready : InnerReady q full CB parent child pointer state)
    (hp : parent < preparedSize q full) (hc : child ≤ preparedSize q full) :
    state.heap (CB + 64) < preparedSize q full ∧ state.heap (CB + 65) ≤ preparedSize q full ∧
      state.heap (CB + 69) ≤ preparedSize q full ∧ state.heap (CB + 66) ≤ preparedSize q full - 1 := by
  rw [ready.parent_cell, ready.child_cell, ready.degree_cell, ready.flat_cell]
  exact ⟨hp, hc, rowList_length_le q full parent child hc, scanList_length_le q full hq hl parent child hp hc⟩

theorem small_value_fits32 (N q value : Nat) (hv : value ≤ N * q + N + q + 640) :
    Fits (indexWidth 32 N q) value := by
  have h := PA17WordBounds023.fits_mono_bits
    (PA17WordBounds023.indexWidth_mono_factor 16 32 N q (by decide)) (fits_checker_register_bound N q)
  exact hv.trans_lt h

theorem mass_fits32 (q : Nat) (full : List (Finset (Fin q))) : Fits (indexWidth 32 full.length q) (mass q full) :=
  small_value_fits32 full.length q _ (by unfold mass; omega)

theorem preparedSize_fits32 (q : Nat) (full : List (Finset (Fin q))) :
    Fits (indexWidth 32 full.length q) (preparedSize q full) :=
  (preparedSize_le_mass q full).trans_lt (mass_fits32 q full)

theorem fixed_offset_fits32 (N q offset : Nat) (ho : offset ≤ 533) : Fits (indexWidth 32 N q) offset :=
  small_value_fits32 N q offset (by omega)

/-- Raw copied prefix plus t degree words and t-1 children. Every access
is before this linear high-bank end (end pointers themselves are allowed). -/
def highCacheEnd (CB M : Nat) : Nat := CB + 512 + 21 + 7 * M

theorem output_end_le (CB M t : Nat) (ht : t ≤ M) :
    childrenBase CB M t + (t - 1) ≤ highCacheEnd CB M := by
  unfold childrenBase degreeBase highCacheEnd
  omega

theorem highCacheEnd_le_allowance (CB N q : Nat) :
    highCacheEnd CB (N + q + 1) ≤ CB + 512 + PA06A19PrepareControlBank017.cacheAllowance N q := by
  unfold highCacheEnd PA06A19PrepareControlBank017.cacheAllowance PA06A19PrepareControlBank017.mass
  omega

def actualPackedWords (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  packedCapacityWords q (CompactControllerClaims.capacityWords 8192 full.length q (preparedSize q full))
    (indexWidth 32 full.length q)

def actualControlBase (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  PA06A19PrepareControlBank017.controlBase full.length q (preparedSize q full) (actualPackedWords q full)

def actualAllocation (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  PA06A19PrepareControlBank017.allocation full.length q (preparedSize q full) (actualPackedWords q full)

/-- Exact original commonF8192 allocation; no extra heap or caller room
eligibility is introduced. These definitions unfold to the actual C/P. -/
theorem highCacheEnd_actual_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    highCacheEnd (actualControlBase q full) (mass q full) < actualAllocation q full ∧
      Fits (indexWidth 32 full.length q) (actualAllocation q full) ∧
      Fits (indexWidth 32 full.length q) (highCacheEnd (actualControlBase q full) (mass q full)) := by
  have ht : 0 < preparedSize q full := by
    have h := PA06A19PrepareControlBank017.treeSize_pos full hq
    simpa only [CompactControllerClaims.treeSize, Nat.ne_of_gt hq, ite_false] using h
  have hr := PA06A19PrepareControlBank017.cache_end_room full.length q (preparedSize q full)
    (actualPackedWords q full) hq ht
  have hl := highCacheEnd_le_allowance (actualControlBase q full) full.length q
  have he : highCacheEnd (actualControlBase q full) (mass q full) < actualAllocation q full := by
    simpa only [PA06A19PrepareControlBank017.cacheBase, actualControlBase, actualAllocation] using hl.trans_lt hr
  have hf : Fits (indexWidth 32 full.length q) (actualAllocation q full) := by
    have h := PA06A19PrepareControlBank017.actual_allocation_fits full
    simpa only [actualAllocation, actualPackedWords, CompactControllerClaims.treeSize,
      Nat.ne_of_gt hq, ite_false] using h
  exact ⟨he, hf, he.trans hf⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
