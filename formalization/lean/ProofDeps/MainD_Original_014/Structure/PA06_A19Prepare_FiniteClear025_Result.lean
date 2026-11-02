module

public import Structure.PA06_A19Prepare_FiniteClear025_Safety

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

/-! Uncompiled concrete finite Word zero/frame consequence. The all-prefix
safety is independently proved by025Safety; these are actual final stores,
not an initial-zero premise for the original preprocessor. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear025Result

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawTreePreprocessingClaims
open PA06A19PrepareFiniteClear025 PA06A19PrepareFiniteClear025Safety

theorem clear_word_zero_frame {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (left right : List PackingOp) (base length : Nat) (before : WordState bits)
    (hone : Fits bits 1) (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbase : (before.register .index).toNat = base) (hlen : (before.register .total).toNat = length)
    (hend : Fits bits (base + length)) (hroom : base + length ≤ heapWords)
    (hpcCode : Fits bits (5 * (left ++ programAt left.length ++ right).length))
    (hcode : WordsFit bits (packingCode (left ++ programAt left.length ++ right))) :
    let code := left ++ programAt left.length ++ right
    let after := packingRun rom code (7 * length + 5) before
    (∀ index < length, after.heap (BitVec.ofNat bits (base + index)) = 0) ∧
      (∀ point : BitVec bits, point.toNat < base ∨ base + length ≤ point.toNat →
        after.heap point = before.heap point) ∧
      after.register .address = before.register .address ∧
      after.pc.toNat = 5 * (left.length + 10) ∧ after.halted = false := by
  let code := left ++ programAt left.length ++ right
  let natural := PA06A19PrepareNodeBit015.wordView before
  have hw := clear_word_fullwidth rom heapWords left right base length before hone hpc ha hbase hlen
    hend hroom hpcCode hcode (7 * length + 5) le_rfl
  have hn := clear_run rom left right base length natural hpc ha hbase hlen
  dsimp only at hw hn ⊢
  refine ⟨?_, ?_, hw.2.2.1, ?_, hw.2.1⟩
  · intro index hi
    rw [hw.1]
    change BitVec.ofNat bits ((natRun rom code (7 * length + 5) natural).heap
      (BitVec.ofNat bits (base + index)).toNat) = 0
    have hf : Fits bits (base + index) := (by omega : base + index ≤ base + length).trans_lt hend
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf, hn.1 index hi]
    rfl
  · intro point hout
    rw [hw.1]
    change BitVec.ofNat bits ((natRun rom code (7 * length + 5) natural).heap point.toNat) = before.heap point
    rw [hn.2.1 point.toNat hout]
    simp only [natural, PA06A19PrepareNodeBit015.wordView, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hw.1]
    change (BitVec.ofNat bits (natRun rom code (7 * length + 5) natural).pc).toNat = _
    rw [BitVec.toNat_ofNat, hn.2.2.2.1]
    exact Nat.mod_eq_of_lt ((by
      simp only [List.length_append, programAt_length]
      omega : 5 * (left.length + 10) ≤ 5 * (left ++ programAt left.length ++ right).length).trans_lt hpcCode)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear025Result
