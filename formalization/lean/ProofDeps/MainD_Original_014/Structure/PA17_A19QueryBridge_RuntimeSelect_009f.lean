module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009a

/-! Fixed reverse-parent-push continuation. The scalar in `.value` is the
actual packed-reader result. Header8/10/11/12 contain runtime-written node,
candidate/count/parent bases. No capacity array or callback answer is ROM
data, and no index-cell value is globally assumed small. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def pushProgram : List PackingOp :=
  [.base (.base (.constant .index 8)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .old .index)), .base (.base (.constant .flag 1)),
   .base (.subtract .fresh .old .flag),
   .base (.base (.constant .index 11)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .index .index)), .base (.base (.add .index .index .fresh)),
   .base (.base (.loadHeap .total .index)), .base (.subtract .flag .value .total),
   .base (.base (.constant .index 12)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .index .index)), .base (.base (.add .index .index .old)),
   .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .index 10)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .index .index)), .base (.base (.add .index .index .total)),
   .base (.base (.loadHeap .fresh .index)),
   .base (.base (.select .value .flag .old .fresh)),
   .base (.base (.select .value .total .value .fresh)),
   .base (.base (.storeHeap .index .value))]

theorem pushProgram_length : pushProgram.length = 24 := rfl
theorem pushProgram_straight : StraightProgram pushProgram := by
  simp [pushProgram, StraightProgram, StraightOp]

def pushedValue {bits : Nat} (node parent cap count : Nat) (old : BitVec bits) : BitVec bits :=
  if parent = 0 then old else if cap - count = 0 then old else BitVec.ofNat bits (node + 1)

theorem pushProgram_result {bits : Nat} (rom : PhysicalROM)
    (header candidates counts parents node parent cap count : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hn : Fits bits (node + 1)) (hparentFit : Fits bits parent)
    (hcap : Fits bits cap) (hcount : Fits bits count)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hv : state.register .value = BitVec.ofNat bits cap)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits candidates)
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadCount : state.heap (BitVec.ofNat bits (counts + node)) = BitVec.ofNat bits count)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent) :
    let after := executeOps rom pushProgram state
    after.register .address = BitVec.ofNat bits header ∧
      after.register .index = BitVec.ofNat bits (candidates + parent) ∧
      after.register .value = pushedValue node parent cap count (state.heap (BitVec.ofNat bits (candidates + parent))) ∧
      after.heap = Function.update state.heap (BitVec.ofNat bits (candidates + parent))
        (pushedValue node parent cap count (state.heap (BitVec.ofNat bits (candidates + parent)))) := by
  have hd : Fits bits (cap - count) := (Nat.sub_le _ _).trans_lt hcap
  simp +decide [pushProgram, pushedValue, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hh, hv, hnode, hcandidates, hcounts, hparents, hreadCount, hreadParent,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hparentFit, Nat.mod_eq_of_lt hcap, Nat.mod_eq_of_lt hcount, Nat.mod_eq_of_lt hd]

theorem pushedValue_toNat_le {bits : Nat} (node parent cap count : Nat) (old : BitVec bits) (bound : Nat)
    (hn : node + 1 ≤ bound) (ho : old.toNat ≤ bound) : (pushedValue node parent cap count old).toNat ≤ bound := by
  unfold pushedValue
  split
  · exact ho
  · split
    · exact ho
    · exact (Nat.mod_le _ _).trans hn

theorem pushProgram_fetched {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (origin : Nat)
    (hbound : origin + pushProgram.length ≤ containing.length)
    (hcode : ∀ i (hi : i < pushProgram.length), containing[origin + i]'(by omega) = pushProgram[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    packingRun rom containing 24 state = executeOps rom pushProgram state := by
  simpa only [pushProgram_length] using straight_segment rom containing pushProgram origin hbound hcode pushProgram_straight
    hw hpc state hp ha

theorem pushProgram_active_exit {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (origin : Nat)
    (hbound : origin + pushProgram.length ≤ containing.length)
    (hcode : ∀ i (hi : i < pushProgram.length), containing[origin + i]'(by omega) = pushProgram[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    (packingRun rom containing 24 state).halted = false ∧
      (packingRun rom containing 24 state).pc = BitVec.ofNat bits (5 * (origin + 24)) := by
  rw [pushProgram_fetched rom containing origin hbound hcode hw hpc state hp ha]
  refine ⟨by rw [executeOps_halted, ha], ?_⟩
  rw [executeOps_pc rom pushProgram state pushProgram_straight, hp, pushProgram_length, BitVec.ofNat_add_ofNat]
  congr 1

theorem pushProgram_trace_le {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom containing 24 state).length ≤ 288 := packingDynamicTrace_length_le rom containing 24 state

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
