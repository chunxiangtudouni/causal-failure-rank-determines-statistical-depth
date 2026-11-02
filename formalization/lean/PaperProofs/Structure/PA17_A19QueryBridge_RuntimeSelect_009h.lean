module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009f

/-! Runtime initialization of the selector's local header cells.
All dimensions, row and selected budget are read from actual input/heap.
This fixed38op block supplies the reverse-parent loop, without trusting
incoming scratch words or changing PSTR's workspace W0..15. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def preparePush : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .flag 1)), .base (.base (.add .fresh .total .flag)),
   .base (.base (.constant .index 8)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .total)), .base (.base (.add .old .total .fresh)),
   .base (.subtract .old .address .old),
   .base (.base (.constant .index 11)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .old)), .base (.subtract .old .address .fresh),
   .base (.base (.constant .index 12)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .old)), .base (.base (.constant .index 1)),
   .base (.base (.loadROM .input .old .index)), .base (.base (.constant .flag 2)),
   .base (.base (.add .old .old .flag)), .base (.base (.add .old .old .old)),
   .base (.base (.constant .flag 16)), .base (.base (.add .old .old .flag)),
   .base (.base (.add .old .address .old)),
   .base (.base (.constant .index 10)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index .old)), .base (.base (.loadHeap .old .address)),
   .base (.base (.constant .index 6)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .flag .index)), .arithmetic .multiply .flag .flag .fresh,
   .base (.base (.add .old .old .flag)), .base (.base (.constant .flag 1)),
   .base (.base (.add .old .old .flag)), .base (.base (.constant .index 9)),
   .base (.base (.add .index .address .index)), .base (.base (.storeHeap .index .old))]

theorem preparePush_length : preparePush.length = 38 := rfl
theorem preparePush_straight : StraightProgram preparePush := by
  simp [preparePush, StraightProgram, StraightOp]

def preparedPushHeap {bits : Nat} (q size header row budget : Nat) (heap : BitVec bits → BitVec bits) :=
  Function.update (Function.update (Function.update (Function.update (Function.update heap
    (BitVec.ofNat bits (header + 8)) (BitVec.ofNat bits size))
    (BitVec.ofNat bits (header + 11)) (BitVec.ofNat bits (header - (size + (size + 1)))))
    (BitVec.ofNat bits (header + 12)) (BitVec.ofNat bits (header - (size + 1))))
    (BitVec.ofNat bits (header + 10)) (BitVec.ofNat bits (childBase header q)))
    (BitVec.ofNat bits (header + 9)) (BitVec.ofNat bits (row + budget * (size + 1) + 1))

theorem preparePush_result {bits : Nat} (rom : PhysicalROM) (q size header row budget : Nat) (state : WordState bits)
    (hroom : Fits bits (childBase header q + size + 1)) (hlower : size + (size + 1) ≤ header) (hbudget : budget ≤ q + 1)
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hq : (rom.words .input).getD 1 0 = q) (hh : state.register .address = BitVec.ofNat bits header)
    (hrow : state.heap (BitVec.ofNat bits header) = BitVec.ofNat bits row)
    (hselected : state.heap (BitVec.ofNat bits (header + 6)) = BitVec.ofNat bits budget) :
    let after := executeOps rom preparePush state
    after.register .address = BitVec.ofNat bits header ∧
      after.register .fresh = BitVec.ofNat bits (size + 1) ∧
      after.register .old = BitVec.ofNat bits (row + budget * (size + 1) + 1) ∧
      after.heap = preparedPushHeap q size header row budget state.heap := by
  change (rom.words .input)[1]?.getD 0 = q at hq
  have ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    have he := congrArg (BitVec.ofNat bits) hsize
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he
  have hs : Fits bits (size + 1) := (show size + 1 ≤ childBase header q + size + 1 by omega).trans_lt hroom
  have ht2 : Fits bits (size + (size + 1)) :=
    (show size + (size + 1) ≤ childBase header q + size + 1 by unfold childBase; omega).trans_lt hroom
  have hheader : Fits bits header := (show header ≤ childBase header q + size + 1 by unfold childBase; omega).trans_lt hroom
  have hb : Fits bits budget := (show budget ≤ childBase header q + size + 1 by unfold childBase; omega).trans_lt hroom
  have h1 : Fits bits 1 := (show 1 ≤ childBase header q + size + 1 by omega).trans_lt hroom
  have he (i j : Nat) (hi : i ≤ 12) (hj : j ≤ 12) :
      BitVec.ofNat bits (header + i) = BitVec.ofNat bits (header + j) ↔ i = j := by
    rw [ofNat_injective_of_fit _ _
      ((show header + i ≤ childBase header q + size + 1 by unfold childBase; omega).trans_lt hroom)
      ((show header + j ≤ childBase header q + size + 1 by unfold childBase; omega).trans_lt hroom)]
    omega
  have h0ne (i : Nat) (hi : i ≤ 12) (hp : 0 < i) :
      BitVec.ofNat bits header ≠ BitVec.ofNat bits (header + i) := by
    apply (ofNat_injective_of_fit _ _ hheader
      ((show header + i ≤ childBase header q + size + 1 by unfold childBase; omega).trans_lt hroom)).not.mpr
    omega
  have hchild : header + (q + 2 + (q + 2) + 16) = header + 16 + 2 * (q + 2) := by omega
  simp +decide (disch := omega) [preparePush, preparedPushHeap, childBase, executeOps, packingExecuteOp, wordOp, wordInstruction,
    packingArithmetic, Function.update_apply, hh, ht, hq, hrow, hselected, BitVec.ofNat_add_ofNat, he,
    h0ne 8 (by decide) (by decide), h0ne 10 (by decide) (by decide), h0ne 11 (by decide) (by decide), h0ne 12 (by decide) (by decide), hchild,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht2,
    Nat.mod_eq_of_lt hheader, Nat.mod_eq_of_lt hb]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
