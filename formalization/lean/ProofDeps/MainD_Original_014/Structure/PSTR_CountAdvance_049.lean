module

public import Structure.PSTR_HD_CountWorkspace_025
public import Structure.PSTR_ReplyCapacity_025

/-! The outer counter update is actual RAM code. It reads the degree which
the node kernel wrote atW4, and the actual node/offset counters atW14/W15.
It writes only those two counters, preserving width/mask, counts and parent
buffers. No initialized counter is added to original HeapRepresents. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountAdvance

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM

def advance : List PackingOp :=
  [.base (.base (.constant .total 4)),
   .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .old .address)),
   .base (.base (.constant .total 11)),
   .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .fresh .address)),
   .base (.base (.add .fresh .fresh .old)),
   .base (.base (.storeHeap .address .fresh)),
   .base (.base (.constant .total 1)),
   .base (.subtract .address .address .total),
   .base (.base (.loadHeap .index .address)),
   .base (.base (.add .index .index .total)),
   .base (.base (.storeHeap .address .index))]

def program : List PackingOp := PSTRCountWorkspace.program ++ advance

def nextHeap {bits : Nat} (workspace node offset degree : Nat) (heap : BitVec bits → BitVec bits) :
    BitVec bits → BitVec bits :=
  Function.update (Function.update heap (BitVec.ofNat bits (workspace + 15))
    (BitVec.ofNat bits (offset + degree))) (BitVec.ofNat bits (workspace + 14)) (BitVec.ofNat bits (node + 1))

theorem advance_length : advance.length = 13 := rfl
theorem program_length : program.length = 32 := rfl
theorem program_straight : StraightProgram program := by
  simp [program, PSTRCountWorkspace.program, advance, StraightProgram, StraightOp]

theorem advance_data {bits : Nat} (rom : PhysicalROM) (workspace node offset degree : Nat)
    (state : WordState bits) (ha : state.register .address = BitVec.ofNat bits workspace)
    (hroom : Fits bits (workspace + 15))
    (hdegree : state.heap (BitVec.ofNat bits (workspace + 4)) = BitVec.ofNat bits degree)
    (hnode : state.heap (BitVec.ofNat bits (workspace + 14)) = BitVec.ofNat bits node)
    (hoffset : state.heap (BitVec.ofNat bits (workspace + 15)) = BitVec.ofNat bits offset) :
    let after := executeOps rom advance state
    after.register .value = state.register .value ∧ after.register .index = BitVec.ofNat bits (node + 1) ∧
      after.register .fresh = BitVec.ofNat bits (offset + degree) ∧
      after.heap = nextHeap workspace node offset degree state.heap := by
  have hone : 1 < 2 ^ bits := by unfold Fits at hroom; omega
  have h14 : Fits bits (workspace + 14) := (show workspace + 14 ≤ workspace + 15 by omega).trans_lt hroom
  have hne : BitVec.ofNat bits (workspace + 14) ≠ BitVec.ofNat bits (workspace + 15) :=
    (ofNat_injective_of_fit _ _ h14 hroom).not.mpr (by omega)
  have h15 : workspace + 4 + 11 = workspace + 15 := by omega
  have hsub : workspace + 15 - 1 = workspace + 14 := by omega
  simp +decide only [advance, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, ha, BitVec.ofNat_add_ofNat, h15,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hroom, Nat.mod_eq_of_lt hone,
    hsub, hne, hdegree, hnode, hoffset, nextHeap, and_self]

theorem advance_prefix_frame {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace) (hroom : Fits bits (workspace + 15))
    (address : Nat) (hfit : Fits bits address)
    (hout : address < workspace + 14 ∨ workspace + 16 ≤ address)
    (count : Nat) (hc : count ≤ 13) :
    (executeOps rom (advance.take count) state).heap (BitVec.ofNat bits address) =
      state.heap (BitVec.ofNat bits address) := by
  have hone : 1 < 2 ^ bits := by unfold Fits at hroom; omega
  have h14 : Fits bits (workspace + 14) := (show workspace + 14 ≤ workspace + 15 by omega).trans_lt hroom
  have hn14 : BitVec.ofNat bits address ≠ BitVec.ofNat bits (workspace + 14) :=
    (ofNat_injective_of_fit _ _ hfit h14).not.mpr (by omega)
  have hn15 : BitVec.ofNat bits address ≠ BitVec.ofNat bits (workspace + 15) :=
    (ofNat_injective_of_fit _ _ hfit hroom).not.mpr (by omega)
  have h15 : workspace + 4 + 11 = workspace + 15 := by omega
  have hsub : workspace + 15 - 1 = workspace + 14 := by omega
  interval_cases count <;>
    simp +decide only [advance, List.take_succ_cons, List.take_zero, executeOps,
      packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
      ha, BitVec.ofNat_add_ofNat, h15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hroom,
      Nat.mod_eq_of_lt hone, hsub, hn14, hn15]

theorem execute_advance {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords node offset degree : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : Fits bits (PSTRCountWorkspace.base q full capWords bits + 15))
    (hdegree : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 4)) = BitVec.ofNat bits degree)
    (hnode : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 14)) = BitVec.ofNat bits node)
    (hoffset : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 15)) = BitVec.ofNat bits offset) :
    let after := executeOps (callInput q full command) program state
    after.register .value = state.register .value ∧ after.register .index = BitVec.ofNat bits (node + 1) ∧
      after.register .fresh = BitVec.ofNat bits (offset + degree) ∧
      after.heap = nextHeap (PSTRCountWorkspace.base q full capWords bits) node offset degree state.heap := by
  let rom := callInput q full command
  let located := executeOps rom PSTRCountWorkspace.program state
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords state hb hq rep
  have hh := locating.2.2.2.2.2.1
  have data := advance_data rom (PSTRCountWorkspace.base q full capWords bits) node offset degree located
    locating.1 hroom (by rw [hh]; exact hdegree) (by rw [hh]; exact hnode) (by rw [hh]; exact hoffset)
  dsimp only
  rw [program, executeOps_append]
  exact ⟨data.1.trans locating.2.1, data.2.1, data.2.2.1, by rw [data.2.2.2, hh]⟩

theorem containing_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + program.length ≤ whole.length)
    (hcode : ∀ i (hi : i < program.length), whole[start + i]'(by omega) = program[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 32 state = executeOps rom program state :=
  PSTRWordSegments.straight_segment rom whole program start hbound hcode program_straight hw hpcfit state hp ha

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 32 state).length ≤ 384 :=
  packingDynamicTrace_length_le rom whole 32 state

end PaperProofs.Structure.LaminarTree.PSTRCountAdvance
