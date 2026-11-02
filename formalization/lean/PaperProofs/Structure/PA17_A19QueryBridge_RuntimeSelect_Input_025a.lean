module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ba
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Semantics_019e

/-! Same-call original Inputs supply physical parent/count/source facts.
The payload vector reads the ORIGINAL decoded heap at the selected entry,
including every arbitrary VOID payload word. No child/tool answer is input. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelectInput025

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeSelect009

def payloadBase (rowBase budget size : Nat) : Nat := rowBase + budget * (size + 1) + 1

def actualPayloadCapacity {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords rowBase budget : Nat) (heap : BitVec bits → BitVec bits) :
    IndexedCapacity (prepareNormalization q full).indexed :=
  Vector.ofFn (fun node : (prepareNormalization q full).indexed.NodeId =>
    logicalHeap q capWords heap (payloadBase rowBase budget (treeSize q full) + node.val))

theorem actualPayloadCapacity_get {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords rowBase budget : Nat) (heap : BitVec bits → BitVec bits)
    (node : (prepareNormalization q full).indexed.NodeId) :
    (actualPayloadCapacity full capWords rowBase budget heap).get node =
      logicalHeap q capWords heap (payloadBase rowBase budget (treeSize q full) + node.val) := by
  exact cache_get_ofFn _ node

theorem sources_of_inputs {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords rowBase budget : Nat) (counts : IndexedCapacity (prepareNormalization q full).indexed)
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (hi : PA17QueryTests009.Inputs (prepareNormalization q full).indexed
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + 1)
      rowBase counts row node (logicalHeap q capWords heap)) :
    let W := PSTRQueryLayout.physicalWorkspace full capWords bits
    SelectionSources full counts (actualPayloadCapacity full capWords rowBase budget heap) capWords
      (payloadBase rowBase budget (treeSize q full)) (PSTRQueryLayout.countsBase W)
      (PSTRQueryLayout.parentsBase W (treeSize q full)) heap := by
  dsimp only
  constructor
  · intro target
    exact (PA17A19RuntimeTests010.logical_parent_word full capWords (treeSize q full) (target.val + 1) heap hq).symm.trans
      (hi.parents.2 target)
  · intro target
    exact (PA17A19RuntimeTests010.logical_counts_word full capWords target.val heap hq).symm.trans (hi.counts target)
  · intro target
    exact (actualPayloadCapacity_get full capWords rowBase budget heap target).symm

theorem parent_bound_of_inputs {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords rowBase : Nat) (counts : IndexedCapacity (prepareNormalization q full).indexed)
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (hi : PA17QueryTests009.Inputs (prepareNormalization q full).indexed
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + 1)
      rowBase counts row node (logicalHeap q capWords heap)) :
    ∀ index < treeSize q full,
      (heap (BitVec.ofNat bits (PSTRQueryLayout.parentsBase
        (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + (index + 1)))).toNat ≤ treeSize q full := by
  have hs : (prepareNormalization q full).indexed.nodes.size = treeSize q full := by
    simp only [treeSize, ne_of_gt hq, ite_false]
  intro index hindex
  let target : (prepareNormalization q full).indexed.NodeId := ⟨index, by omega⟩
  rw [← PA17A19RuntimeTests010.logical_parent_word full capWords (treeSize q full) (index + 1) heap hq]
  change logicalHeap q capWords heap
    (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + (target.val + 1)) ≤ treeSize q full
  rw [hi.parents.2 target]
  simpa only [hs] using UniformNormalizationRAM.encodedNode_le (prepareNormalization q full).indexed
    ((prepareNormalization q full).indexed.parents.get target)

theorem parentInputs_of_inputs {bits q origin : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords rowBase budget : Nat)
    (counts : IndexedCapacity (prepareNormalization q full).indexed)
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (node : Option (prepareNormalization q full).indexed.NodeId) (state : WordState bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) = lowMask bits (CapacityBits.width q))
    (hi : PA17QueryTests009.Inputs (prepareNormalization q full).indexed
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + 1)
      rowBase counts row node (logicalHeap q capWords state.heap))
    (hbudget : budget ≤ q + 1)
    (hselected : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header
      (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 6)) = BitVec.ofNat bits budget)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header
      (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let W := PSTRQueryLayout.physicalWorkspace full capWords bits
    let H := PSTRQueryLayout.header W (treeSize q full)
    ParentInputs full configuration origin capWords H (payloadBase rowBase budget (treeSize q full))
      (PSTRQueryLayout.countsBase W) (PSTRQueryLayout.parentsBase W (treeSize q full))
      (treeSize q full) rowBase budget state := by
  dsimp only
  have slots := PA17A19RuntimeTestsSemantics019.inputs_word_slots full capWords rowBase counts row node state hq hi
  refine ⟨rep, hwidth, hmask, parent_bound_of_inputs full capWords rowBase counts row node state.heap hq hi,
    ?_, ?_, rfl, hbudget, slots.1, hselected, hh, hp, ha⟩
  · unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  · unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase
    omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelectInput025
