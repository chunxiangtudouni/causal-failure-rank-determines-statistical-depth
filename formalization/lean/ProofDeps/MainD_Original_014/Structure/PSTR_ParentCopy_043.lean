module

public import Structure.PSTR_ParentSentinel_042
public import Structure.PSTR_HD_CountWorkspace_025

/-! One fixed block copies ONE original encoded parent to the separate
sentinel array. It actually reads the cached field and computes W and the
destination from raw/header data. The outer traversal supplies only its
ordinary node register, and must execute this block for all nodes. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRParentCopy

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM
open PSTRStaticLayout PSTRStaticHeap PSTRQueryLayout

def suffix : List PackingOp :=
  [.base (.base (.constant .total 0)),
   .base (.base (.loadHeap .total .total)),
   .base (.base (.constant .flag 16)),
   .base (.base (.add .total .total .flag)),
   .base (.base (.add .total .total .index)),
   .base (.base (.constant .flag 1)),
   .base (.base (.add .total .total .flag)),
   .base (.base (.add .address .address .total)),
   .base (.base (.storeHeap .address .value))]

def program : List PackingOp :=
  PSTRStaticFields.program ⟨1, by decide⟩ ++ PSTRCountWorkspace.program ++ suffix

theorem suffix_length : suffix.length = 9 := rfl
theorem program_length : program.length = 50 := rfl
theorem program_straight : StraightProgram program := by
  simp [program, PSTRStaticFields.program, PSTRCountWorkspace.program, suffix, StraightProgram, StraightOp]

theorem index_frame {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom program state).register .index = state.register .index := rfl

theorem suffix_heap {bits : Nat} (rom : PhysicalROM) (workspace size node : Nat) (state : WordState bits)
    (hw : state.register .address = BitVec.ofNat bits workspace)
    (hn : state.register .index = BitVec.ofNat bits node)
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size) :
    (executeOps rom suffix state).heap = Function.update state.heap
      (BitVec.ofNat bits (parentsBase workspace size + node + 1)) (state.register .value) := by
  have he : workspace + (size + 16 + node + 1) = parentsBase workspace size + node + 1 := by
    unfold parentsBase countsBase
    omega
  simp +decide only [suffix, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hw, hn, ht, BitVec.ofNat_add_ofNat, he]

theorem execute_parent {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) (hN : Fits bits full.length)
    (hi : state.register .index = BitVec.ofNat bits node.val) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let workspace := PSTRCountWorkspace.base q full capWords bits
    (executeOps (callInput q full command) program state).heap = Function.update state.heap
      (BitVec.ofNat bits (parentsBase workspace size + node.val + 1))
      (BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed
        ((prepareNormalization q full).indexed.parents.get node))) := by
  let rom := callInput q full command
  let loaded := executeOps rom (PSTRStaticFields.program ⟨1, by decide⟩) state
  let located := executeOps rom PSTRCountWorkspace.program loaded
  have reading := PSTRStaticFields.execute_field full command configuration capWords state
    ⟨1, by decide⟩ node.val hb hq rep hN (by simp [chunks]) hi
  have hv := reading.1
  change loaded.register .value = BitVec.ofNat bits
    (((List.finRange (prepareNormalization q full).indexed.nodes.size).map
      (fun other => encodedNode (prepareNormalization q full).indexed
        ((prepareNormalization q full).indexed.parents.get other)))[node.val]) at hv
  rw [mapped_finRange_get] at hv
  have loaded_rep : HeapRepresents q full capWords configuration loaded.heap := by rw [reading.2.2.2]; exact rep
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords loaded hb hq loaded_rep
  obtain ⟨haddr, hvalue, hindex, _hold, _hfresh, hheap, _hhalt⟩ := locating
  have hnode : located.register .index = BitVec.ofNat bits node.val := hindex.trans (reading.2.2.1.trans hi)
  have htree : located.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (prepareNormalization q full).indexed.nodes.size := by
    rw [hheap, reading.2.2.2]
    simpa only [treeSize, ne_of_gt hq, ite_false] using (headers full configuration capWords state.heap rep).1
  dsimp only
  rw [program, executeOps_append, executeOps_append,
    suffix_heap rom (PSTRCountWorkspace.base q full capWords bits) _ node.val located haddr hnode htree,
    hheap, reading.2.2.2, hvalue, hv]

theorem before_store_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 49) :
    (executeOps rom (program.take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem prefix_frame {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) (hN : Fits bits full.length)
    (hi : state.register .index = BitVec.ofNat bits node.val)
    (hroom : Fits bits (parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + (prepareNormalization q full).indexed.nodes.size))
    (address : Nat) (ha : address < parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + node.val + 1)
    (count : Nat) (hc : count ≤ 50) :
    (executeOps (callInput q full command) (program.take count) state).heap (BitVec.ofNat bits address) =
      state.heap (BitVec.ofNat bits address) := by
  by_cases hbefore : count ≤ 49
  · rw [before_store_heap _ state count hbefore]
  · have he : count = 50 := by omega
    subst count
    rw [List.take_of_length_le (show program.length ≤ 50 by rw [program_length]),
      execute_parent full command configuration capWords state node hb hq rep hN hi]
    have hn := node.isLt
    have hfit : Fits bits address := (show address ≤ parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + (prepareNormalization q full).indexed.nodes.size by omega).trans_lt hroom
    have htarget : Fits bits (parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + node.val + 1) := (by omega :
      parentsBase (PSTRCountWorkspace.base q full capWords bits) (prepareNormalization q full).indexed.nodes.size + node.val + 1 ≤
        parentsBase (PSTRCountWorkspace.base q full capWords bits) (prepareNormalization q full).indexed.nodes.size +
          (prepareNormalization q full).indexed.nodes.size).trans_lt hroom
    rw [Function.update_of_ne ((ofNat_injective_of_fit _ _ hfit htarget).not.mpr (by omega))]

theorem containing_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + program.length ≤ whole.length)
    (hcode : ∀ i (hi : i < program.length), whole[start + i]'(by omega) = program[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 50 state = executeOps rom program state :=
  PSTRWordSegments.straight_segment rom whole program start hbound hcode program_straight hw hpcfit state hp ha

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 50 state).length ≤ 600 :=
  packingDynamicTrace_length_le rom whole 50 state

end PaperProofs.Structure.LaminarTree.PSTRParentCopy
