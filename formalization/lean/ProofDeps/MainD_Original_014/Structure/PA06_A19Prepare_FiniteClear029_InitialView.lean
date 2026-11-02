module

public import Structure.PA06_A19Prepare_FiniteClear025_Result
public import Structure.PA06_A19Prepare_FiniteClear025_View

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear029InitialView

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawTreePreprocessingClaims
open AlgorithmClaims.PackedCapacityRAM
open CompactControllerClaims (dataHeap)
open PA06A19PrepareFiniteClear025 PA06A19PreparePackedView013

/-- One actual contiguous finite clear supplies both packed words (including
lookahead) and the ordinary builder domain. The zero-view premise is produced
by real stores, rather than assumed of the original caller. -/
theorem clear_word_initial_view {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (left right : List PackingOp) (q C0 C I : Nat) (before : WordState bits)
    (hq : 0 < q) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hC : C0 ≤ C) (hI : 0 < I) (hone : Fits bits 1)
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbase : (before.register .index).toNat = 4)
    (hlen : (before.register .total).toNat = packedCapacityWords q C bits + I)
    (hend : Fits bits (4 + (packedCapacityWords q C bits + I)))
    (hroom : 4 + (packedCapacityWords q C bits + I) ≤ heapWords)
    (hpcCode : Fits bits (5 * (left ++ programAt left.length ++ right).length))
    (hcode : WordsFit bits (packingCode (left ++ programAt left.length ++ right))) :
    let P := packedCapacityWords q C bits
    let code := left ++ programAt left.length ++ right
    let after := packingRun rom code (7 * (P + I) + 5) before
    (∀ a < C0 + I, view q C0 C (4 + P) after.heap a = 0) ∧
      CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap after.heap)) ∧
      (∀ point : BitVec bits, point.toNat < 4 ∨ 4 + (P + I) ≤ point.toNat →
        after.heap point = before.heap point) ∧
      after.register .address = before.register .address ∧
      after.pc.toNat = 5 * (left.length + 10) ∧ after.halted = false := by
  let P := packedCapacityWords q C bits
  let code := left ++ programAt left.length ++ right
  let after := packingRun rom code (7 * (P + I) + 5) before
  have actual := PA06A19PrepareFiniteClear025Result.clear_word_zero_frame rom heapWords
    left right 4 (P + I) before hone hpc ha hbase hlen hend hroom hpcCode hcode
  dsimp only at actual ⊢
  have packed : ∀ word ≤ P, after.heap (BitVec.ofNat bits (4 + word)) = 0 := by
    intro word hword
    exact actual.1 word (by omega)
  have ordinary : ∀ index < I, after.heap (BitVec.ofNat bits (4 + P + index)) = 0 := by
    intro index hindex
    simpa only [Nat.add_assoc] using actual.1 (P + index) (by omega)
  exact ⟨(fun a ha => PA06A19PrepareFiniteClear025View.view_zero_of_finite_words
      q C0 C I after.heap hq hb hw hC packed ordinary a ha),
    PA06A19PrepareFiniteClear025View.capacity_bounded_of_finite_zero q C after.heap hq hb hw packed,
    actual.2⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear029InitialView
