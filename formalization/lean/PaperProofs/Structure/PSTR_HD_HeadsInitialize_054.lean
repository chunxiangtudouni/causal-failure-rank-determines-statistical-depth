module

public import PaperProofs.Structure.PSTR_HD_HeadsGuard_053

/-! Real first-return initialization, selected by the actual stage=0.
No preexisting heads scratch value is assumed. Original query ROM supplies q. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def headsInit : List PackingOp :=
  [.base (.base (.storeHeap .address .value)),
   .base (.base (.constant .total 1)),
   .base (.base (.add .address .address .total)),
   .base (.base (.constant .flag 0)),
   .base (.base (.storeHeap .address .flag)),
   .base (.base (.add .address .address .total)),
   .base (.base (.constant .total 8)),
   .base (.base (.add .flag .address .total)),
   .base (.base (.storeHeap .address .flag)),
   .base (.base (.constant .total 1)),
   .base (.base (.add .address .address .total)),
   .base (.base (.loadROM .input .flag .total)),
   .base (.base (.constant .total 2)),
   .base (.base (.add .flag .flag .total)),
   .base (.subtract .flag .flag .value),
   .base (.base (.storeHeap .address .flag)),
   .base (.base (.constant .total 3)),
   .base (.subtract .address .address .total),
   .base (.base (.constant .total 8)),
   .base (.base (.add .flag .address .total)),
   .base (.base (.storeHeap .flag .value))]

def initHeap {bits : Nat} (endpoint q rank : Nat) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update (Function.update (Function.update (Function.update (Function.update heap
    (BitVec.ofNat bits endpoint) (BitVec.ofNat bits rank))
    (BitVec.ofNat bits (endpoint + 1)) (BitVec.ofNat bits 0))
    (BitVec.ofNat bits (endpoint + 2)) (BitVec.ofNat bits (endpoint + 10)))
    (BitVec.ofNat bits (endpoint + 3)) (BitVec.ofNat bits (q + 2 - rank)))
    (BitVec.ofNat bits (endpoint + 8)) (BitVec.ofNat bits rank)

theorem headsInit_length : headsInit.length = 21 := rfl

theorem headsInit_straight : StraightProgram headsInit := by simp [headsInit, StraightProgram, StraightOp]

theorem execute_headsInit {bits : Nat} (rom : PhysicalROM) (endpoint q rank : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (he : Fits bits (endpoint + 3)) (hr : Fits bits rank) (hq : Fits bits (q + 2))
    (hp : state.register .address = BitVec.ofNat bits endpoint) (hv : state.register .value = BitVec.ofNat bits rank)
    (hraw : (rom.words .input).getD 1 0 = q) :
    let after := executeOps rom headsInit state
    after.heap = initHeap endpoint q rank state.heap ∧
      after.register .address = BitVec.ofNat bits endpoint ∧
      after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
      after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
      after.halted = state.halted := by
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (by omega)
  have h3 : (BitVec.ofNat bits 3).toNat = 3 := Nat.mod_eq_of_lt (by omega)
  have hen : (BitVec.ofNat bits (endpoint + 3)).toNat = endpoint + 3 := Nat.mod_eq_of_lt he
  have hrn : (BitVec.ofNat bits rank).toNat = rank := Nat.mod_eq_of_lt hr
  have hqn : (BitVec.ofNat bits (q + 2)).toNat = q + 2 := Nat.mod_eq_of_lt hq
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩ <;>
    simp +decide only [headsInit, initHeap, executeOps, packingExecuteOp, wordOp, wordInstruction,
      Function.update_apply, ↓reduceIte, hp, hv, hraw, h1, h3, hen, hrn, hqn,
      BitVec.ofNat_add_ofNat, Nat.add_assoc, Nat.add_sub_cancel_right]

theorem headsInit_prefix_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (endpoint heapWords : Nat) (state : WordState bits) (hb : 8 ≤ bits)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (he : Fits bits (endpoint + 3)) (hroom : endpoint + 8 < heapWords)
    (count : Nat) (hc : count < headsInit.length) :
    packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (headsInit.take count) state) headsInit[count] := by
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (by omega)
  have h3 : (BitVec.ofNat bits 3).toNat = 3 := Nat.mod_eq_of_lt (by omega)
  have hen : (BitVec.ofNat bits (endpoint + 3)).toNat = endpoint + 3 := Nat.mod_eq_of_lt he
  have hs (offset : Nat) (ho : offset ≤ 8) : (BitVec.ofNat bits (endpoint + offset)).toNat < heapWords :=
    (Nat.mod_le _ _).trans_lt (by omega)
  have h0 : (BitVec.ofNat bits endpoint).toNat < heapWords := by simpa using hs 0 (by decide)
  have hin : 1 < (callInput q full command).input.length := by simp [callInput, RawTreePreprocessingClaims.rawIncidenceROM]
  change count < 21 at hc
  interval_cases count <;>
    simp_all +decide [headsInit, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, PhysicalROM.words, BitVec.ofNat_add_ofNat, Nat.add_assoc]; omega

theorem headsInit_prefix_frame {bits : Nat} (rom : PhysicalROM) (endpoint : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hp : state.register .address = BitVec.ofNat bits endpoint)
    (he : Fits bits (endpoint + 8)) (physical : Nat) (hf : Fits bits physical)
    (hout : physical < endpoint ∨ endpoint + 9 ≤ physical)
    (count : Nat) (hc : count ≤ headsInit.length) :
    (executeOps rom (headsInit.take count) state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have h3 : (BitVec.ofNat bits 3).toNat = 3 := Nat.mod_eq_of_lt (by omega)
  have hen : (BitVec.ofNat bits (endpoint + 3)).toNat = endpoint + 3 :=
    Nat.mod_eq_of_lt ((show endpoint + 3 ≤ endpoint + 8 by omega).trans_lt he)
  have hn (offset : Nat) (ho : offset ≤ 8) :
      BitVec.ofNat bits physical ≠ BitVec.ofNat bits (endpoint + offset) :=
    (ofNat_injective_of_fit _ _ hf ((show endpoint + offset ≤ endpoint + 8 by omega).trans_lt he)).not.mpr (by omega)
  have h0 : BitVec.ofNat bits physical ≠ BitVec.ofNat bits endpoint := by simpa using hn 0 (by decide)
  change count ≤ 21 at hc
  interval_cases count <;>
    simp (disch := omega) [headsInit, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hp, h3, hen, BitVec.ofNat_add_ofNat, Nat.add_assoc, Function.update_apply, hn]

theorem containing_headsInit {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + headsInit.length ≤ whole.length)
    (hcode : ∀ i (hi : i < headsInit.length), whole[start + i]'(by omega) = headsInit[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 21 state = executeOps rom headsInit state :=
  straight_segment rom whole headsInit start hbound hcode headsInit_straight hwords hpcfit state hp ha

theorem headsInit_trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 21 state).length ≤ 252 := packingDynamicTrace_length_le rom whole 21 state

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
