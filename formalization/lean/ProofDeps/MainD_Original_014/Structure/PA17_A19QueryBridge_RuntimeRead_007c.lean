module

public import Structure.PA17_A19QueryBridge_RuntimeRead_007b

/-! Reload the actual per-call width/mask cache at W12/W13 in constant time.
The incoming value register is the computed logical table address; address
is the actual query header. All other incoming registers are arbitrary. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRead007

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PSTRWordSegments

def cacheLoad : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadHeap .old .index)),
   .base (.base (.constant .index 2)), .arithmetic .multiply .old .old .index,
   .base (.base (.constant .index 17)), .base (.base (.add .old .old .index)),
   .base (.subtract .fresh .address .old), .base (.base (.constant .index 12)),
   .base (.base (.add .index .fresh .index)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .old 1)), .base (.base (.add .index .index .old)),
   .base (.base (.loadHeap .flag .index)), .base (.base (.constant .old 0)),
   .base (.base (.add .address .value .old))]

def cachedProgram : List PackingOp := cacheLoad ++ program

theorem cacheLoad_length : cacheLoad.length = 15 := rfl
theorem cachedProgram_length : cachedProgram.length = 58 := rfl

theorem cacheLoad_straight : StraightProgram cacheLoad := by
  simp [cacheLoad, StraightProgram, StraightOp]

theorem cacheLoad_noStore : ∀ op ∈ cacheLoad, HeapPreservingOp op := by
  simp [cacheLoad, HeapPreservingOp]

theorem cachedProgram_straight : StraightProgram cachedProgram := by
  intro op ho
  rcases List.mem_append.mp ho with ho | ho
  · exact cacheLoad_straight op ho
  · exact program_straight op ho

theorem cachedProgram_noStore : ∀ op ∈ cachedProgram, HeapPreservingOp op := by
  intro op ho
  rcases List.mem_append.mp ho with ho | ho
  · exact cacheLoad_noStore op ho
  · exact program_noStore op ho

theorem cacheLoad_result {bits : Nat} (rom : PhysicalROM)
    (workspace size : Nat) (state : WordState bits) (hb : 8 ≤ bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size)) :
    let after := executeOps rom cacheLoad state
    after.register .address = state.register .value ∧
    after.register .value = state.register .value ∧
    after.register .total = state.heap (BitVec.ofNat bits (workspace + 12)) ∧
    after.register .flag = state.heap (BitVec.ofNat bits (workspace + 13)) ∧
    after.heap = state.heap := by
  have hsmall : 2 < 2 ^ bits := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
    omega
  have hmul : Fits bits (size * 2 + 17) := by
    apply (show size * 2 + 17 ≤ PSTRQueryLayout.header workspace size from ?_).trans_lt hroom
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have hdiff : PSTRQueryLayout.header workspace size - (size * 2 + 17) = workspace := by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  simp +decide only [cacheLoad, executeOps, packingExecuteOp, wordOp, wordInstruction,
    packingArithmetic, Function.update_apply, ↓reduceIte, hsize, hh,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, BitVec.ofNat_add_ofNat,
    Nat.mod_eq_of_lt hroom, Nat.mod_eq_of_lt hmul, hdiff, BitVec.add_zero]

theorem execute_cached {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hscalar : (state.register .value).toNat < capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hf : Fits bits heapWords)
    (hheader : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) < heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))) :
    let after := executeOps (callInput q full command) cachedProgram state
    after.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)) ∧
    (after.register .value).toNat = logicalHeap q capWords state.heap (state.register .value).toNat ∧
    after.heap = state.heap ∧ after.halted = state.halted := by
  let rom := callInput q full command
  let loaded := executeOps rom cacheLoad state
  have hl := cacheLoad_result rom (PSTRQueryLayout.physicalWorkspace full capWords bits)
    (treeSize q full) state hb (hheader.trans hf) rep.1 hh
  have hrep : HeapRepresents q full capWords configuration loaded.heap := by
    rw [hl.2.2.2.2]
    exact rep
  have halloc : PSTRQueryLayout.physicalWorkspace full capWords bits < heapWords := by
    unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase at hheader
    omega
  have hr := execute_result full command configuration capWords heapWords loaded hb hq hw hrep
    (by rw [hl.1]; exact hscalar) hs hf halloc
    (hl.2.2.1.trans hwidth) (hl.2.2.2.1.trans hmask)
  dsimp only
  rw [cachedProgram, executeOps_append]
  refine ⟨hr.1, ?_, hr.2.2.1.trans hl.2.2.2.2, executeOps_halted rom (cacheLoad ++ program) state⟩
  rw [hr.2.1, hl.1, hl.2.2.2.2]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRead007
