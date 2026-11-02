module

public import PaperProofs.Structure.PSTR_HD_CountFrame_026

/-! Actual entry spills the four internally produced count-kernel values.
No value is loaded from a new ROM field. The locator preserves the values
while computing the original metadata-end workspace with fixed code. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountWorkspace

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine AlgorithmClaims.PackedCapacityRAM PSTRStaticHeap

def spillProgram : List PackingOp :=
  [.base (.base (.constant .flag 1)),
   .base (.base (.storeHeap .address .old)),
   .base (.base (.add .address .address .flag)),
   .base (.base (.storeHeap .address .fresh)),
   .base (.base (.add .address .address .flag)),
   .base (.base (.storeHeap .address .index)),
   .base (.base (.add .address .address .flag)),
   .base (.base (.storeHeap .address .value))]

def entryHeap {bits : Nat} (workspace : Nat) (state : WordState bits) : BitVec bits → BitVec bits :=
  Function.update
    (Function.update
      (Function.update
        (Function.update state.heap (BitVec.ofNat bits workspace) (state.register .old))
        (BitVec.ofNat bits (workspace + 1)) (state.register .fresh))
      (BitVec.ofNat bits (workspace + 2)) (state.register .index))
    (BitVec.ofNat bits (workspace + 3)) (state.register .value)

def bootstrap : List PackingOp := program ++ spillProgram

theorem spill_length : spillProgram.length = 8 := rfl
theorem bootstrap_length : bootstrap.length = 27 := rfl
theorem spill_straight : StraightProgram spillProgram := by simp [spillProgram, StraightProgram, StraightOp]
theorem bootstrap_straight : StraightProgram bootstrap := by
  intro op ho
  rcases List.mem_append.mp ho with hl | hr
  · exact program_straight op hl
  · exact spill_straight op hr

theorem execute_spill {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (workspace : Nat)
    (hp : state.register .address = BitVec.ofNat bits workspace) :
    let result := executeOps rom spillProgram state
    result.heap = entryHeap workspace state ∧ result.register .address = BitVec.ofNat bits (workspace + 3) ∧
    result.register .value = state.register .value ∧ result.register .index = state.register .index ∧
    result.register .old = state.register .old ∧ result.register .fresh = state.register .fresh ∧
    result.halted = state.halted := by
  simp +decide [spillProgram, entryHeap, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem execute_bootstrap {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap) :
    let result := executeOps (callInput q full command) bootstrap state
    result.heap = entryHeap (base q full capWords bits) state ∧
    result.register .address = BitVec.ofNat bits (base q full capWords bits + 3) ∧
    result.register .value = state.register .value ∧ result.register .index = state.register .index ∧
    result.register .old = state.register .old ∧ result.register .fresh = state.register .fresh ∧
    result.halted = state.halted := by
  rw [bootstrap, executeOps_append]
  have hl := execute_base full command configuration capWords state hb hq rep
  have hs := execute_spill (callInput q full command) _ (base q full capWords bits) hl.1
  dsimp only at hl hs ⊢
  simpa only [entryHeap, hl.2.1, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2.1,
    hl.2.2.2.2.2.1, hl.2.2.2.2.2.2] using hs

theorem entry_prefix_frame {bits : Nat} (workspace : Nat) (state : WordState bits)
    (hf : Fits bits (workspace + 3)) :
    ∀ physical < workspace, entryHeap workspace state (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  intro physical hp
  unfold entryHeap
  rw [store_prefix_frame _ workspace (workspace + 3) _ (by omega) hf physical hp,
    store_prefix_frame _ workspace (workspace + 2) _ (by omega) ((by omega : workspace + 2 ≤ workspace + 3).trans_lt hf) physical hp,
    store_prefix_frame _ workspace (workspace + 1) _ (by omega) ((by omega : workspace + 1 ≤ workspace + 3).trans_lt hf) physical hp,
    store_prefix_frame _ workspace workspace _ le_rfl ((by omega : workspace ≤ workspace + 3).trans_lt hf) physical hp]

theorem entry_outside {bits : Nat} (workspace : Nat) (state : WordState bits)
    (hf : Fits bits (workspace + 3)) (physical : Nat) (hp : Fits bits physical)
    (hout : physical < workspace ∨ workspace + 4 ≤ physical) :
    entryHeap workspace state (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  unfold entryHeap
  rw [store_other _ (workspace + 3) physical _ hf hp (by omega),
    store_other _ (workspace + 2) physical _ ((by omega : workspace + 2 ≤ workspace + 3).trans_lt hf) hp (by omega),
    store_other _ (workspace + 1) physical _ ((by omega : workspace + 1 ≤ workspace + 3).trans_lt hf) hp (by omega),
    store_other _ workspace physical _ ((by omega : workspace ≤ workspace + 3).trans_lt hf) hp (by omega)]

theorem entry_represents {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 0 < bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 3)) :
    HeapRepresents q full capWords configuration (entryHeap (base q full capWords bits) state) := by
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords
    (base q full capWords bits) state.heap _ hb hq rep bitmap hr hw ?_
    (entry_prefix_frame _ state hw)
  rw [base_metadata_end q full hq capWords bits]
  unfold metadataAddress physicalHeaderWords
  omega

theorem spill_prefix_access {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (workspace heapWords : Nat) (hp : state.register .address = BitVec.ofNat bits workspace)
    (hr : workspace + 3 < heapWords) (count : Nat) (hc : count < spillProgram.length) :
    packingAccessFits rom heapWords (executeOps rom (spillProgram.take count) state) spillProgram[count] := by
  have hs (offset : Nat) (ho : offset ≤ 3) : (BitVec.ofNat bits (workspace + offset)).toNat < heapWords :=
    (Nat.mod_le _ _).trans_lt (by omega)
  have hs0 := hs 0 (by decide)
  simp only [Nat.add_zero] at hs0
  change count < 8 at hc
  interval_cases count <;>
    simp_all +decide [spillProgram, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat, Nat.add_assoc]

end PaperProofs.Structure.LaminarTree.PSTRCountWorkspace
