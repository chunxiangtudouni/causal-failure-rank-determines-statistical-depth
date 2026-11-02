module

public import PaperProofs.Structure.PSTR_HD_ZeroHeadsWord_006

/-! The zero-tool head branch in the original logarithmic finite word width.
Only an actual post-preprocessing HeapRepresents state is consumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRZeroHeads

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingClaims
open PaperProofs.Common.Native.CompactPrice

theorem original_width_eight (N : Nat) : 8 ≤ indexWidth 16 N 0 := by
  have hc : 0 < Nat.clog 2 (N + 0 + 2) := Nat.clog_pos (by decide) (by omega)
  unfold indexWidth
  omega

theorem original_register_fit (N : Nat) : Fits (indexWidth 16 N 0) (N + 128) := by
  have hf := fits_checker_register_bound N 0
  exact lt_of_le_of_lt (by omega) hf

theorem original_footprint_fit (N : Nat) : Fits (indexWidth 16 N 0) (16 * N + 143) := by
  apply fits_indexWidth_of_lt_power
  have hl : 16 * N + 143 ≤ (N + 0 + 2) ^ 2 + 1024 := by
    by_cases h : N ≤ 12
    · nlinarith
    · have hm := Nat.mul_le_mul_left N (show 13 ≤ N by omega)
      nlinarith
  exact hl.trans_lt (quadratic_add_lt_power16 (N + 0 + 2) (by omega))

theorem width_mono (N factor : Nat) (hf : 16 ≤ factor) :
    indexWidth 16 N 0 ≤ indexWidth factor N 0 := Nat.mul_le_mul_right _ hf

theorem original_fit_factor (N factor value : Nat) (hf : 16 ≤ factor)
    (hv : Fits (indexWidth 16 N 0) value) : Fits (indexWidth factor N 0) value :=
  hv.trans_le (Nat.pow_le_pow_right (by decide) (width_mono N factor hf))

theorem original_heapWords_factor (N factor : Nat) (hf : 16 ≤ factor) :
    physicalHeaderWords + packedCapacityWords 0 0 (indexWidth factor N 0) + 16 * (N + 1) = 16 * N + 20 := by
  have hb := (original_width_eight N).trans (width_mono N factor hf)
  have hz : (indexWidth factor N 0 - 1) / indexWidth factor N 0 = 0 := Nat.div_eq_of_lt (by omega)
  simp only [physicalHeaderWords, packedCapacityWords, Nat.zero_mul, Nat.zero_add, hz]
  omega

/-- Complete physical q=0 heads run after the original persistent heap has
been built; preprocessing and the positive-tool branch remain separate.
Every original factor at least 16, including the main factor 32, is covered. -/
theorem zero_heads_original_width (factor : Nat) (hfactor : 16 ≤ factor)
    (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (heap : BitVec (indexWidth factor full.length 0) → BitVec (indexWidth factor full.length 0))
    (hr : HeapRepresents 0 full 0 ⟨0, used, false⟩ heap) :
    let heapWords := physicalHeaderWords + packedCapacityWords 0 0 (indexWidth factor full.length 0) +
      16 * (full.length + 1)
    ∃ steps : Nat, steps ≤ 9 * full.length + 18 ∧
      DynamicRunCorrect heapWords (callInput 0 full .query) program steps heap ∧
      callCost 0 full program .query steps heap ≤ 512 * headWork 0 full ∧
      let result := packingRun (callInput 0 full .query) program steps (packingInitial heap)
      HeapRepresents 0 full 0 ⟨full.length, used, false⟩ result.heap ∧
      (result.register .index).toNat = 6 ∧
      6 + (headWords 0 full used).length ≤ heapWords ∧
      heapWordsAt result.heap 6 (headWords 0 full used).length = headWords 0 full used := by
  dsimp only
  have hf : Fits (indexWidth factor full.length 0)
      ((callInput 0 full .query).size +
        (physicalHeaderWords + packedCapacityWords 0 0 (indexWidth factor full.length 0) + 16 * (full.length + 1)) +
        (packingCode program).length) := by
    rw [zero_query_rom, original_heapWords_factor _ _ hfactor, program_code_length]
    change Fits (indexWidth factor full.length 0) (3 + (16 * full.length + 20) + 120)
    rw [show 3 + (16 * full.length + 20) + 120 = 16 * full.length + 143 by omega]
    exact original_fit_factor _ _ _ hfactor (original_footprint_fit full.length)
  exact physical_zero_heads full used _ heap
    ((original_width_eight full.length).trans (width_mono full.length factor hfactor))
    (original_fit_factor _ _ _ hfactor (original_register_fit full.length))
    (by rw [original_heapWords_factor _ _ hfactor]; omega) hf hr

end PaperProofs.Structure.LaminarTree.PSTRZeroHeads

