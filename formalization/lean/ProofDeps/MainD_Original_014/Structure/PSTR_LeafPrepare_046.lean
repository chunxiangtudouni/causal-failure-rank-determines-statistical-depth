module

public import Structure.PSTR_HD_CountWorkspace_025
public import PaperProofs.Structure.PackedCapacityRAM

/-! Real leaf-reader preparation. The cached metadata address is parked in
an ordinary register, then the fixed W locator is executed, and the width/
mask actually initialized atW12/W13 are reloaded before restoring that
address. No width/mask register answer is assumed at this block's entry. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLeafPrepare

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRStaticLayout PSTRStaticHeap

def parkAddress : List PackingOp :=
  [.base (.base (.constant .fresh 0)), .base (.base (.add .old .address .fresh))]

def loadWidth : List PackingOp :=
  [.base (.base (.constant .flag 12)),
   .base (.base (.add .address .address .flag)),
   .base (.base (.loadHeap .total .address)),
   .base (.base (.constant .fresh 1)),
   .base (.base (.add .address .address .fresh)),
   .base (.base (.loadHeap .flag .address)),
   .base (.base (.constant .fresh 0)),
   .base (.base (.add .address .old .fresh))]

def program : List PackingOp := PSTRStaticFields.program ⟨6, by decide⟩ ++ parkAddress ++
  PSTRCountWorkspace.program ++ loadWidth

theorem program_length : program.length = 51 := rfl
theorem program_straight : StraightProgram program := by
  simp [program, PSTRStaticFields.program, parkAddress, PSTRCountWorkspace.program,
    loadWidth, StraightProgram, StraightOp]

theorem park_registers {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom parkAddress state).register .old = state.register .address ∧
      (executeOps rom parkAddress state).register .index = state.register .index ∧
      (executeOps rom parkAddress state).heap = state.heap := by
  simp +decide only [parkAddress, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, BitVec.add_zero, and_self]

theorem load_registers {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace) :
    let after := executeOps rom loadWidth state
    after.register .address = state.register .old ∧
      after.register .total = state.heap (BitVec.ofNat bits (workspace + 12)) ∧
      after.register .flag = state.heap (BitVec.ofNat bits (workspace + 13)) ∧
      after.register .index = state.register .index ∧ after.heap = state.heap := by
  have h13 : workspace + 12 + 1 = workspace + 13 := by omega
  simp +decide only [loadWidth, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, ha, BitVec.ofNat_add_ofNat, BitVec.add_zero, h13, and_self]

theorem execute_ready {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) (hN : Fits bits full.length)
    (hi : state.register .index = BitVec.ofNat bits node.val)
    (savedWidth : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (savedMask : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q)) :
    let after := executeOps (callInput q full command) program state
    after.register .address = BitVec.ofNat bits
        (metadataAddress q capWords bits (offset q full 6 + node.val)) ∧
      after.register .total = BitVec.ofNat bits (CapacityBits.width q) ∧
      after.register .flag = lowMask bits (CapacityBits.width q) ∧
      after.register .index = BitVec.ofNat bits node.val ∧ after.heap = state.heap := by
  let rom := callInput q full command
  let read := executeOps rom (PSTRStaticFields.program ⟨6, by decide⟩) state
  let parked := executeOps rom parkAddress read
  let located := executeOps rom PSTRCountWorkspace.program parked
  have reading := PSTRStaticFields.execute_field full command configuration capWords state
    ⟨6, by decide⟩ node.val hb hq rep hN (by simp [chunks]) hi
  have parking := park_registers rom read
  have parked_heap : parked.heap = state.heap := parking.2.2.trans reading.2.2.2
  have parked_rep : HeapRepresents q full capWords configuration parked.heap := by rw [parked_heap]; exact rep
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords parked hb hq parked_rep
  have loading := load_registers rom (PSTRCountWorkspace.base q full capWords bits) located locating.1
  have heap : located.heap = state.heap := locating.2.2.2.2.2.1.trans parked_heap
  dsimp only
  rw [program, executeOps_append, executeOps_append, executeOps_append]
  refine ⟨?_, ?_, ?_, ?_, loading.2.2.2.2.trans heap⟩
  · exact loading.1.trans (locating.2.2.2.1.trans (parking.1.trans reading.2.1))
  · rw [loading.2.1, heap, savedWidth]
  · rw [loading.2.2.1, heap, savedMask]
  · exact loading.2.2.2.1.trans (locating.2.2.1.trans (parking.2.1.trans (reading.2.2.1.trans hi)))

theorem all_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 51) :
    (executeOps rom (program.take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem containing_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + program.length ≤ whole.length)
    (hcode : ∀ i (hi : i < program.length), whole[start + i]'(by omega) = program[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 51 state = executeOps rom program state :=
  PSTRWordSegments.straight_segment rom whole program start hbound hcode program_straight hw hpcfit state hp ha

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 51 state).length ≤ 612 :=
  packingDynamicTrace_length_le rom whole 51 state

end PaperProofs.Structure.LaminarTree.PSTRLeafPrepare
