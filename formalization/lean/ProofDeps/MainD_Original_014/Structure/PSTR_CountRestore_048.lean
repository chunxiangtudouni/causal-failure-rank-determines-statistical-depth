module

public import Structure.PSTR_HD_CountWorkspace_025

/-! Real transition from the leaf reader to the node-count kernel. Actual
outer-control slotsW14/W15 supply node/flat-child offset; B=W16 is computed.
The incoming VALUE is preserved, so the actual leafBitmap result is used. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountRestore

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

def restore : List PackingOp :=
  [.base (.base (.constant .total 14)),
   .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .index .address)),
   .base (.base (.constant .total 1)),
   .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .fresh .address)),
   .base (.base (.add .old .address .total))]

def program : List PackingOp := PSTRCountWorkspace.program ++ restore

theorem program_length : program.length = 26 := rfl
theorem program_straight : StraightProgram program := by
  simp [program, PSTRCountWorkspace.program, restore, StraightProgram, StraightOp]

theorem restore_registers {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace) :
    let after := executeOps rom restore state
    after.register .value = state.register .value ∧
      after.register .index = state.heap (BitVec.ofNat bits (workspace + 14)) ∧
      after.register .fresh = state.heap (BitVec.ofNat bits (workspace + 15)) ∧
      after.register .old = BitVec.ofNat bits (workspace + 16) ∧ after.heap = state.heap := by
  have h15 : workspace + 14 + 1 = workspace + 15 := by omega
  have h16 : workspace + 15 + 1 = workspace + 16 := by omega
  simp +decide only [restore, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, ha, BitVec.ofNat_add_ofNat, h15, h16, and_self]

theorem execute_entry {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap) :
    let workspace := PSTRCountWorkspace.base q full capWords bits
    let after := executeOps (callInput q full command) program state
    after.register .value = state.register .value ∧
      after.register .index = state.heap (BitVec.ofNat bits (workspace + 14)) ∧
      after.register .fresh = state.heap (BitVec.ofNat bits (workspace + 15)) ∧
      after.register .old = BitVec.ofNat bits (workspace + 16) ∧ after.heap = state.heap := by
  let rom := callInput q full command
  let located := executeOps rom PSTRCountWorkspace.program state
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords state hb hq rep
  have restoring := restore_registers rom (PSTRCountWorkspace.base q full capWords bits) located locating.1
  dsimp only
  rw [program, executeOps_append]
  exact ⟨restoring.1.trans locating.2.1,
    restoring.2.1.trans (congrFun locating.2.2.2.2.2.1 _),
    restoring.2.2.1.trans (congrFun locating.2.2.2.2.2.1 _),
    restoring.2.2.2.1, restoring.2.2.2.2.trans locating.2.2.2.2.2.1⟩

theorem all_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 26) :
    (executeOps rom (program.take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem containing_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + program.length ≤ whole.length)
    (hcode : ∀ i (hi : i < program.length), whole[start + i]'(by omega) = program[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 26 state = executeOps rom program state :=
  PSTRWordSegments.straight_segment rom whole program start hbound hcode program_straight hw hpcfit state hp ha

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 26 state).length ≤ 312 :=
  packingDynamicTrace_length_le rom whole 26 state

end PaperProofs.Structure.LaminarTree.PSTRCountRestore
