module

public import Structure.PSTR_HD_CountWorkspace_025
public import Structure.PSTR_LeafUsed_027

/-! Real selected-error repair entry AFTER saving the old reply. Actual
scratchW11 contains its selected-tool encoding and actualW12 the width
computed on this call. Those are internal materialization facts, not new
original caller fields. The fixed program computes marker address/width/
reply cursor without receiving any of those register answers as input. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRepairEntry

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

def loadControls : List PackingOp :=
  [.base (.base (.constant .flag 11)),
   .base (.base (.add .address .address .flag)),
   .base (.base (.loadHeap .value .address)),
   .base (.base (.constant .index 1)),
   .base (.base (.add .address .address .index)),
   .base (.base (.loadHeap .total .address)),
   .base (.subtract .flag .address .index)]

def program : List PackingOp := PSTRCountWorkspace.program ++ loadControls ++ PSTRLeafUsed.setup

theorem controls_length : loadControls.length = 7 := rfl
theorem program_length : program.length = 42 := rfl
theorem program_straight : StraightProgram program := by
  simp [program, PSTRCountWorkspace.program, loadControls, PSTRLeafUsed.setup, StraightProgram, StraightOp]

theorem load_registers {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hroom : Fits bits (workspace + 12))
    (ha : state.register .address = BitVec.ofNat bits workspace) :
    let after := executeOps rom loadControls state
    after.register .value = state.heap (BitVec.ofNat bits (workspace + 11)) ∧
      after.register .total = state.heap (BitVec.ofNat bits (workspace + 12)) ∧
      after.register .flag = BitVec.ofNat bits (workspace + 11) ∧ after.heap = state.heap := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have hone : 1 < 2 ^ bits := by omega
  have h12 : workspace + 11 + 1 = workspace + 12 := by omega
  have hsub : workspace + 12 - 1 = workspace + 11 := by omega
  simp +decide only [loadControls, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, ha, BitVec.ofNat_add_ofNat, h12,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hroom, Nat.mod_eq_of_lt hone, hsub, and_self]

theorem execute_entry {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits) (tool : Fin q)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : Fits bits (PSTRCountWorkspace.base q full capWords bits + 12))
    (savedTool : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 11)) =
      BitVec.ofNat bits (tool.val + 1))
    (savedWidth : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hN1 : Fits bits (full.length + 1)) (hq2 : Fits bits (q + 2))
    (ht1 : Fits bits (treeSize q full + 1)) (hprod : Fits bits ((full.length + 1) * (q + 2))) :
    let after := executeOps (callInput q full command) program state
    after.register .address = BitVec.ofNat bits (tableWords full.length q (treeSize q full) + tool.val) ∧
      after.register .total = BitVec.ofNat bits (CapacityBits.width q) ∧
      after.register .flag = BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 11) ∧
      after.heap = state.heap := by
  let rom := callInput q full command
  let located := executeOps rom PSTRCountWorkspace.program state
  let controlled := executeOps rom loadControls located
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords state hb hq rep
  have controls := load_registers rom (PSTRCountWorkspace.base q full capWords bits) located hb hroom locating.1
  have heap : controlled.heap = state.heap := controls.2.2.2.trans locating.2.2.2.2.2.1
  have ht : (controlled.heap (BitVec.ofNat bits 0)).toNat = treeSize q full := by rw [heap]; exact rep.1
  have hfit : Fits bits (tool.val + 1) := (show tool.val + 1 ≤ q + 2 by have hn := tool.isLt; omega).trans_lt hq2
  have hlabel : (controlled.register .value).toNat = tool.val + 1 := by
    rw [controls.1, locating.2.2.2.2.2.1, savedTool, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  have haddr := PSTRLeafUsed.setup_address rom controlled full.length q (treeSize q full) tool.val
    hb (by rfl) (by rfl) ht hlabel hN1 hq2 ht1 hprod
  dsimp only
  rw [program, executeOps_append, executeOps_append]
  refine ⟨haddr, ?_, ?_, ?_⟩
  · rw [PSTRLeafUsed.setup_width, controls.2.1, locating.2.2.2.2.2.1, savedWidth]
  · rw [PSTRLeafUsed.setup_mask, controls.2.2.1]
  · exact (PSTRLeafUsed.setup_heap rom controlled).trans heap

theorem all_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 42) :
    (executeOps rom (program.take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem containing_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + program.length ≤ whole.length)
    (hcode : ∀ i (hi : i < program.length), whole[start + i]'(by omega) = program[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 42 state = executeOps rom program state :=
  PSTRWordSegments.straight_segment rom whole program start hbound hcode program_straight hw hpcfit state hp ha

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 42 state).length ≤ 504 :=
  packingDynamicTrace_length_le rom whole 42 state

end PaperProofs.Structure.LaminarTree.PSTRRepairEntry
