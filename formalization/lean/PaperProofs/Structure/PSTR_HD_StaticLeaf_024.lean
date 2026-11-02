module

public import PaperProofs.Structure.PSTR_HD_StaticFieldsSafety_023

/-! The leaf label is loaded from the same original cached metadata with
actual address formation. Packed used-bit reading remains a separate block. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRStaticFields

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRStaticLayout PSTRStaticHeap

theorem execute_leaf {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) (hN : Fits bits full.length)
    (hi : state.register .index = BitVec.ofNat bits node.val) :
    let result := executeOps (callInput q full command) (program ⟨6, by decide⟩) state
    result.register .value = BitVec.ofNat bits
      (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
        | none => 0 | some tool => tool.val + 1) ∧
      result.register .index = state.register .index ∧ result.heap = state.heap := by
  have hr := execute_field full command configuration capWords state ⟨6, by decide⟩ node.val hb hq rep hN
    (by simp [chunks]) hi
  have hv := hr.1
  change (executeOps (callInput q full command) (program ⟨6, by decide⟩) state).register .value =
    BitVec.ofNat bits (((List.finRange (prepareNormalization q full).indexed.nodes.size).map
      (fun other => match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get other with
        | none => 0 | some tool => tool.val + 1))[node.val]) at hv
  rw [mapped_finRange_get] at hv
  exact ⟨hv, hr.2.2⟩

theorem standalone_leaf {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) (hN : Fits bits full.length)
    (hi : state.register .index = BitVec.ofNat bits node.val)
    (hpc : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let result := packingRun (callInput q full command) (program ⟨6, by decide⟩) 23 state
    result.halted = true ∧ result.register .value = BitVec.ofNat bits
      (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
        | none => 0 | some tool => tool.val + 1) ∧
      result.register .index = state.register .index ∧ result.heap = state.heap := by
  rw [show 23 = (program ⟨6, by decide⟩).length + 1 from rfl,
    packingRun_executeOps_halt _ _ state (program_straight _) (code_fit _ hb) (pc_fit _ hb) hpc ha]
  exact ⟨rfl, execute_leaf full command configuration capWords state node hb hq rep hN hi⟩

end PaperProofs.Structure.LaminarTree.PSTRStaticFields
