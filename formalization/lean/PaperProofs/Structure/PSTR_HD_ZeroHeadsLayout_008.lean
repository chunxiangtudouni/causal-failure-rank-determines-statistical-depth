module

public import PaperProofs.Structure.PSTR_HD_ZeroHeadsOriginal_007

/-! The q=0 actual head program in larger original shared layouts. Scratch
constants are implementation choices, never extra task/input fields. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRZeroHeads

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingClaims
open PaperProofs.Common.Native.CompactPrice

theorem shared_footprint_lt_power (N scratch : Nat) (hs : scratch ≤ 65536) :
    scratch * (N + 1) + 127 < (N + 2) ^ 32 := by
  have hb : 2 ≤ N + 2 := by omega
  have hp : 65536 ≤ (N + 2) ^ 16 := Nat.pow_le_pow_left hb 16
  have hn : N + 2 ≤ (N + 2) ^ 16 := by
    calc
      _ = (N + 2) ^ 1 := by rw [pow_one]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hm := Nat.mul_le_mul hp hn
  have hs' := Nat.mul_le_mul_right (N + 1) hs
  have hlt : scratch * (N + 1) + 127 < 65536 * (N + 2) := by omega
  apply hlt.trans_le
  simpa only [← pow_add] using hm

theorem shared_footprint_fit (N factor scratch : Nat) (hf : 32 ≤ factor) (hs : scratch ≤ 65536) :
    Fits (indexWidth factor N 0) (scratch * (N + 1) + 127) := by
  have hv : Fits (indexWidth 32 N 0) (scratch * (N + 1) + 127) :=
    fits_indexWidth_of_lt_power 32 N 0 _ (shared_footprint_lt_power N scratch hs)
  have hw : indexWidth 32 N 0 ≤ indexWidth factor N 0 := Nat.mul_le_mul_right _ hf
  exact hv.trans_le (Nat.pow_le_pow_right (by decide) hw)

theorem shared_heapWords (N factor scratch : Nat) (hf : 32 ≤ factor) :
    physicalHeaderWords + packedCapacityWords 0 0 (indexWidth factor N 0) + scratch * (N + 1) =
      scratch * (N + 1) + 4 := by
  have hb := (original_width_eight N).trans (width_mono N factor (by omega))
  have hz : (indexWidth factor N 0 - 1) / indexWidth factor N 0 = 0 := Nat.div_eq_of_lt (by omega)
  simp only [physicalHeaderWords, packedCapacityWords, Nat.zero_mul, Nat.zero_add, hz]
  omega

/-- No word-size/footprint premise is added to an original q=0 task. The
same physical code works with all shared scratch constants from 4 to 65536. -/
theorem zero_heads_shared_layout (factor scratch : Nat) (hf : 32 ≤ factor)
    (hslo : 4 ≤ scratch) (hshi : scratch ≤ 65536)
    (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (heap : BitVec (indexWidth factor full.length 0) → BitVec (indexWidth factor full.length 0))
    (hr : HeapRepresents 0 full 0 ⟨0, used, false⟩ heap) :
    let heapWords := physicalHeaderWords + packedCapacityWords 0 0 (indexWidth factor full.length 0) +
      scratch * (full.length + 1)
    ∃ steps : Nat, steps ≤ 9 * full.length + 18 ∧
      DynamicRunCorrect heapWords (callInput 0 full .query) program steps heap ∧
      callCost 0 full program .query steps heap ≤ 512 * headWork 0 full ∧
      let result := packingRun (callInput 0 full .query) program steps (packingInitial heap)
      HeapRepresents 0 full 0 ⟨full.length, used, false⟩ result.heap ∧
      (result.register .index).toNat = 6 ∧
      6 + (headWords 0 full used).length ≤ heapWords ∧
      heapWordsAt result.heap 6 (headWords 0 full used).length = headWords 0 full used := by
  dsimp only
  have hfoot : Fits (indexWidth factor full.length 0)
      ((callInput 0 full .query).size +
        (physicalHeaderWords + packedCapacityWords 0 0 (indexWidth factor full.length 0) + scratch * (full.length + 1)) +
        (packingCode program).length) := by
    rw [zero_query_rom, shared_heapWords _ _ _ hf, program_code_length]
    change Fits (indexWidth factor full.length 0) (3 + (scratch * (full.length + 1) + 4) + 120)
    rw [show 3 + (scratch * (full.length + 1) + 4) + 120 = scratch * (full.length + 1) + 127 by omega]
    exact shared_footprint_fit _ _ _ hf hshi
  have hheap : full.length + 8 ≤ physicalHeaderWords + packedCapacityWords 0 0 (indexWidth factor full.length 0) +
      scratch * (full.length + 1) := by
    rw [shared_heapWords _ _ _ hf]
    have hm := Nat.mul_le_mul_right (full.length + 1) hslo
    omega
  exact physical_zero_heads full used _ heap
    ((original_width_eight full.length).trans (width_mono full.length factor (by omega)))
    (original_fit_factor _ _ _ (by omega) (original_register_fit full.length)) hheap hfoot hr

end PaperProofs.Structure.LaminarTree.PSTRZeroHeads
