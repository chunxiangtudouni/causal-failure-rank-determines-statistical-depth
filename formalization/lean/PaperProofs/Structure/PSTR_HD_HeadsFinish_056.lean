module

public import PaperProofs.Structure.PSTR_HD_HeadsAppend_055

/-! Real terminal count/header write and actual output-base register. The
only heap write is output[1]; rank and ordered stage entries already persist. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def headsFinish : List PackingOp :=
  [.base (.base (.constant .index 8)),
   .base (.base (.add .index .address .index)),
   .base (.base (.constant .total 1)),
   .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .value .address)),
   .base (.base (.add .address .index .total)),
   .base (.base (.storeHeap .address .value))]

theorem headsFinish_length : headsFinish.length = 7 := rfl

theorem headsFinish_straight : StraightProgram headsFinish := by simp [headsFinish, StraightProgram, StraightOp]

theorem execute_headsFinish {bits : Nat} (rom : PhysicalROM) (endpoint count : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (hk : state.heap (BitVec.ofNat bits (endpoint + 1)) = BitVec.ofNat bits count) :
    let after := executeOps rom headsFinish state
    after.heap = Function.update state.heap (BitVec.ofNat bits (endpoint + 9)) (BitVec.ofNat bits count) ∧
      after.register .index = BitVec.ofNat bits (outputBase endpoint) ∧ after.register .value = BitVec.ofNat bits count ∧
      after.register .address = BitVec.ofNat bits (endpoint + 9) ∧
      after.register .old = state.register .old ∧ after.register .fresh = state.register .fresh ∧
      after.register .flag = state.register .flag ∧ after.halted = state.halted := by
  simp +decide [headsFinish, outputBase, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, hk, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem headsFinish_prefix_access {bits : Nat} (rom : PhysicalROM) (endpoint heapWords : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits endpoint) (hroom : endpoint + 9 < heapWords)
    (count : Nat) (hc : count < headsFinish.length) :
    packingAccessFits rom heapWords (executeOps rom (headsFinish.take count) state) headsFinish[count] := by
  have h1 : (BitVec.ofNat bits (endpoint + 1)).toNat < heapWords := (Nat.mod_le _ _).trans_lt (by omega)
  have h9 : (BitVec.ofNat bits (endpoint + 9)).toNat < heapWords := (Nat.mod_le _ _).trans_lt hroom
  change count < 7 at hc
  interval_cases count <;>
    simp_all +decide [headsFinish, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem headsFinish_prefix_frame {bits : Nat} (rom : PhysicalROM) (endpoint : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (he : Fits bits (endpoint + 9)) (physical : Nat) (hf : Fits bits physical) (hne : physical ≠ endpoint + 9)
    (count : Nat) (hc : count ≤ headsFinish.length) :
    (executeOps rom (headsFinish.take count) state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  have hn : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (endpoint + 9) :=
    (ofNat_injective_of_fit _ _ hf he).not.mpr hne
  change count ≤ 7 at hc
  interval_cases count <;>
    simp (disch := assumption) [headsFinish, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hp, BitVec.ofNat_add_ofNat, Nat.add_assoc, Function.update_apply]

theorem finish_base_toNat {bits : Nat} (rom : PhysicalROM) (endpoint count : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (hk : state.heap (BitVec.ofNat bits (endpoint + 1)) = BitVec.ofNat bits count) (he : Fits bits (endpoint + 9)) :
    ((executeOps rom headsFinish state).register .index).toNat = outputBase endpoint := by
  rw [(execute_headsFinish rom endpoint count state hp hk).2.1, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt ((show outputBase endpoint ≤ endpoint + 9 by unfold outputBase; omega).trans_lt he)

theorem containing_headsFinish {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + headsFinish.length ≤ whole.length)
    (hcode : ∀ i (hi : i < headsFinish.length), whole[start + i]'(by omega) = headsFinish[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 7 state = executeOps rom headsFinish state :=
  straight_segment rom whole headsFinish start hbound hcode headsFinish_straight hwords hpcfit state hp ha

theorem headsFinish_trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 7 state).length ≤ 84 := packingDynamicTrace_length_le rom whole 7 state

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
