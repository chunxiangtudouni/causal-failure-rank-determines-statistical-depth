module

public import PaperProofs.Structure.PSTR_HD_HeadsInitialize_054

/-! Ten actual instructions append the ORIGINAL stage index and update the
real count/cursor slots. The stage comes from the real stage-word probe. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def headsAppend : List PackingOp :=
  [.base (.base (.constant .total 1)),
   .base (.base (.add .index .address .total)),
   .base (.base (.loadHeap .value .index)),
   .base (.base (.add .flag .index .total)),
   .base (.base (.loadHeap .fresh .flag)),
   .base (.base (.storeHeap .fresh .old)),
   .base (.base (.add .value .value .total)),
   .base (.base (.storeHeap .index .value)),
   .base (.base (.add .fresh .fresh .total)),
   .base (.base (.storeHeap .flag .fresh))]

def appendHeap {bits : Nat} (endpoint cursor stage count : Nat) (heap : BitVec bits → BitVec bits) :
    BitVec bits → BitVec bits :=
  Function.update (Function.update (Function.update heap
    (BitVec.ofNat bits cursor) (BitVec.ofNat bits stage))
    (BitVec.ofNat bits (endpoint + 1)) (BitVec.ofNat bits (count + 1)))
    (BitVec.ofNat bits (endpoint + 2)) (BitVec.ofNat bits (cursor + 1))

theorem headsAppend_length : headsAppend.length = 10 := rfl

theorem headsAppend_straight : StraightProgram headsAppend := by simp [headsAppend, StraightProgram, StraightOp]

theorem execute_headsAppend {bits : Nat} (rom : PhysicalROM) (endpoint cursor stage count : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (hs : state.register .old = BitVec.ofNat bits stage)
    (hk : state.heap (BitVec.ofNat bits (endpoint + 1)) = BitVec.ofNat bits count)
    (hc : state.heap (BitVec.ofNat bits (endpoint + 2)) = BitVec.ofNat bits cursor) :
    let after := executeOps rom headsAppend state
    after.heap = appendHeap endpoint cursor stage count state.heap ∧
      after.register .address = BitVec.ofNat bits endpoint ∧ after.register .old = state.register .old ∧
      after.register .value = BitVec.ofNat bits (count + 1) ∧
      after.register .fresh = BitVec.ofNat bits (cursor + 1) ∧
      after.register .index = BitVec.ofNat bits (endpoint + 1) ∧
      after.register .flag = BitVec.ofNat bits (endpoint + 2) ∧ after.halted = state.halted := by
  simp +decide [headsAppend, appendHeap, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, hs, hk, hc, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem headsAppend_prefix_access {bits : Nat} (rom : PhysicalROM) (endpoint cursor heapWords : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (hc : state.heap (BitVec.ofNat bits (endpoint + 2)) = BitVec.ofNat bits cursor)
    (hroom : endpoint + 2 < heapWords) (hcursor : cursor < heapWords)
    (count : Nat) (hcount : count < headsAppend.length) :
    packingAccessFits rom heapWords (executeOps rom (headsAppend.take count) state) headsAppend[count] := by
  have h1 : (BitVec.ofNat bits (endpoint + 1)).toNat < heapWords := (Nat.mod_le _ _).trans_lt (by omega)
  have h2 : (BitVec.ofNat bits (endpoint + 2)).toNat < heapWords := (Nat.mod_le _ _).trans_lt hroom
  have hcur : (BitVec.ofNat bits cursor).toNat < heapWords := (Nat.mod_le _ _).trans_lt hcursor
  change count < 10 at hcount
  interval_cases count <;>
    simp_all +decide [headsAppend, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem headsAppend_prefix_frame {bits : Nat} (rom : PhysicalROM) (endpoint cursor : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (hc : state.heap (BitVec.ofNat bits (endpoint + 2)) = BitVec.ofNat bits cursor)
    (he : Fits bits (endpoint + 2)) (hcursor : Fits bits cursor)
    (physical : Nat) (hf : Fits bits physical)
    (hne1 : physical ≠ endpoint + 1) (hne2 : physical ≠ endpoint + 2) (hnec : physical ≠ cursor)
    (count : Nat) (hcount : count ≤ headsAppend.length) :
    (executeOps rom (headsAppend.take count) state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  have h1w : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (endpoint + 1) :=
    (ofNat_injective_of_fit _ _ hf ((show endpoint + 1 ≤ endpoint + 2 by omega).trans_lt he)).not.mpr hne1
  have h2w : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (endpoint + 2) :=
    (ofNat_injective_of_fit _ _ hf he).not.mpr hne2
  have hcw : BitVec.ofNat bits physical ≠ BitVec.ofNat bits cursor :=
    (ofNat_injective_of_fit _ _ hf hcursor).not.mpr hnec
  change count ≤ 10 at hcount
  interval_cases count <;>
    simp (disch := assumption) [headsAppend, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hp, hc, BitVec.ofNat_add_ofNat, Nat.add_assoc, Function.update_apply]

theorem containing_headsAppend {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + headsAppend.length ≤ whole.length)
    (hcode : ∀ i (hi : i < headsAppend.length), whole[start + i]'(by omega) = headsAppend[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 10 state = executeOps rom headsAppend state :=
  straight_segment rom whole headsAppend start hbound hcode headsAppend_straight hwords hpcfit state hp ha

theorem headsAppend_trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 10 state).length ≤ 120 := packingDynamicTrace_length_le rom whole 10 state

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
