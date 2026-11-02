module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeRanks_008b

/-! The fixed footer writes the four real internal control cells and restores
the original011 rank-register ABI. Its entry is actual loop accumulators, not
supplied callback answers. No scratch value is assumed initialized. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM

def resultHeap {bits : Nat} (header good bad : Nat) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update
    (Function.update
      (Function.update
        (Function.update heap (BitVec.ofNat bits (header + 4)) (BitVec.ofNat bits good))
        (BitVec.ofNat bits (header + 5)) (BitVec.ofNat bits bad))
      (BitVec.ofNat bits (header + 6)) (BitVec.ofNat bits (bad - 1)))
    (BitVec.ofNat bits (header + 7))
    (BitVec.ofNat bits (if (heap (BitVec.ofNat bits (header + 2))).toNat = 0 then 0 else if bad = 0 then 0 else 1))

theorem execute_footer {bits : Nat} (rom : PhysicalROM) (q header good bad : Nat) (state : WordState bits)
    (hroom : Fits bits (header + 16 + 2 * (q + 2)))
    (hg : good ≤ q + 2) (hb : bad ≤ q + 2)
    (hp : state.register .address = BitVec.ofNat bits header)
    (hgood : state.register .value = BitVec.ofNat bits good)
    (hbad : state.register .fresh = BitVec.ofNat bits bad)
    (hq : state.register .total = BitVec.ofNat bits (q + 2)) :
    let after := executeOps rom footer state
    let active := (state.heap (BitVec.ofNat bits (header + 2))).toNat
    after.heap = resultHeap header good bad state.heap ∧
      after.register .old = BitVec.ofNat bits (if active = 0 then q + 2 else good) ∧
      after.register .fresh = BitVec.ofNat bits (if active = 0 then 0 else bad) ∧
      after.register .value = BitVec.ofNat bits (if active = 0 then q + 2 else min good (bad + 1)) ∧
      after.register .index = BitVec.ofNat bits 0 ∧ after.register .address = BitVec.ofNat bits header := by
  have h1 : Fits bits 1 := (show 1 ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  have hgf : Fits bits good := (show good ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  have hbf : Fits bits bad := (show bad ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  have hbf1 : Fits bits (bad + 1) := (show bad + 1 ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  have he (i j : Nat) (hi : i ≤ 7) (hj : j ≤ 7) :
      BitVec.ofNat bits (header + i) = BitVec.ofNat bits (header + j) ↔ i = j := by
    rw [ofNat_injective_of_fit _ _
      ((show header + i ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom)
      ((show header + j ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom)]
    omega
  by_cases ha : (state.heap (BitVec.ofNat bits (header + 2))).toNat = 0
  · have haz : state.heap (BitVec.ofNat bits (header + 2)) = BitVec.ofNat bits 0 := by
      apply BitVec.eq_of_toNat_eq
      simpa using ha
    simp +decide (disch := omega) [footer, resultHeap, executeOps, packingExecuteOp, wordOp, wordInstruction,
      Function.update_apply, hp, hgood, hbad, hq, BitVec.ofNat_add_ofNat, Nat.add_assoc, he,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hgf, Nat.mod_eq_of_lt hbf,
      Nat.mod_eq_of_lt hbf1, haz]
  · simp +decide (disch := omega) [footer, resultHeap, executeOps, packingExecuteOp, wordOp, wordInstruction,
      Function.update_apply, hp, hgood, hbad, BitVec.ofNat_add_ofNat, Nat.add_assoc, he,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hgf, Nat.mod_eq_of_lt hbf,
      Nat.mod_eq_of_lt hbf1, ha]
    constructor
    · by_cases hz : bad = 0 <;> simp [hz]
    · by_cases hgb : good ≤ bad + 1 <;> simp [hgb, Nat.min_def]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008
