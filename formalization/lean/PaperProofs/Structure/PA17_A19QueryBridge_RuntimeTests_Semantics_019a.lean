module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015n
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015q
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeHeader_011g

/-! Actual fixed Tests flags for ORIGINAL IndexedQuery semantics. The word
header and parent bounds are derived from materialized original Inputs. -/

@[expose] public section
set_option maxRecDepth 28000
set_option maxHeartbeats 2800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSemantics019

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem inputs_word_slots {bits q : Nat} (full : List (Finset (Fin q))) (capWords rowBase : Nat)
    (counts : IndexedCapacity (prepareNormalization q full).indexed)
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (node : Option (prepareNormalization q full).indexed.NodeId) (state : WordState bits) (hq : 0 < q)
    (hi : PA17QueryTests009.Inputs (prepareNormalization q full).indexed
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + 1)
      rowBase counts row node (logicalHeap q capWords state.heap)) :
    let H := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
    state.heap (BitVec.ofNat bits H) = BitVec.ofNat bits rowBase ∧
      state.heap (BitVec.ofNat bits (H + 1)) = BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed node) ∧
      encodedNode (prepareNormalization q full).indexed node ≤ treeSize q full ∧
      (∀ e ≤ treeSize q full, logicalHeap q capWords state.heap
        (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full) := by
  have hsize : (prepareNormalization q full).indexed.nodes.size = treeSize q full := by
    simp only [treeSize, ne_of_gt hq, ite_false]
  have hr := (PA17A19RuntimeTests010.logical_header_word full capWords (treeSize q full) 0 state.heap hq).symm
  simp only [Nat.add_zero] at hr
  have hn := (PA17A19RuntimeTests010.logical_header_word full capWords (treeSize q full) 1 state.heap hq).symm
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hv := hr.trans hi.row_pointer
    rw [← hv]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have hv := hn.trans hi.node_pointer
    rw [← hv]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simpa only [hsize] using UniformNormalizationRAM.encodedNode_le (prepareNormalization q full).indexed node
  · intro encoded he
    cases encoded with
    | zero => rw [Nat.add_zero, hi.parents.1]; omega
    | succ index =>
      let target : (prepareNormalization q full).indexed.NodeId := ⟨index, by omega⟩
      change logicalHeap q capWords state.heap
        (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + (target.val + 1)) ≤ treeSize q full
      rw [hi.parents.2 target]
      simpa only [hsize] using UniformNormalizationRAM.encodedNode_le (prepareNormalization q full).indexed
        ((prepareNormalization q full).indexed.parents.get target)

structure SemanticTestsPost {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords rowBase origin : Nat) (counts : IndexedCapacity (prepareNormalization q full).indexed)
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (node : Option (prepareNormalization q full).indexed.NodeId) (before after : WordState bits) : Prop where
  actual : PA17A19RuntimeTests010.OuterLoopPost full capWords rowBase (q + 2)
    (encodedNode (prepareNormalization q full).indexed node) origin before after
  good : ∀ budget < q + 2, after.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 + budget)) =
    BitVec.ofNat bits (bit (IndexedQuery.accepts (prepareNormalization q full).indexed counts (IndexedQuery.entryAt row budget)))
  bad : ∀ budget < q + 2, after.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 + (q + 2) + budget)) =
    BitVec.ofNat bits (bit (IndexedQuery.budgetExtensionTest (prepareNormalization q full).indexed counts row node budget))
  represents : HeapRepresents q full capWords configuration after.heap

theorem actual_tests_semantic {bits q origin : Nat} {containing : List PackingOp}
    (em : PA17A19RuntimeTests010.Embedded bits origin containing)
    (full : List (Finset (Fin q))) (command : Command) (configuration : Configuration q)
    (capWords heapWords rowBase : Nat)
    (counts : IndexedCapacity (prepareNormalization q full).indexed)
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (node : Option (prepareNormalization q full).indexed.NodeId) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q ≤ heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) = lowMask bits (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hi : PA17QueryTests009.Inputs (prepareNormalization q full).indexed
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + 1)
      rowBase counts row node (logicalHeap q capWords state.heap))
    (hrow : rowBase + (q + 2) * (treeSize q full + 1) ≤ capWords) :
    SemanticTestsPost full configuration capWords rowBase origin counts row node state
      (packingRun (callInput q full command) containing (PA17A19RuntimeTests010.steps q (treeSize q full)) state) := by
  have slots := inputs_word_slots full capWords rowBase counts row node state hq hi
  have result := PA17A19RuntimeTests010.actual_tests_from_materialized_header em full command configuration
    capWords heapWords rowBase (encodedNode (prepareNormalization q full).indexed node) state
    hb hq hw rep bitmap hs hf halloc hwidth hmask hh hp ha slots.1 slots.2.1 slots.2.2.1 hrow slots.2.2.2
  have hsize : (prepareNormalization q full).indexed.nodes.size = treeSize q full := by
    simp only [treeSize, ne_of_gt hq, ite_false]
  have hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16) := by
    have hg : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 <
        PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q := by
      unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
      omega
    exact (hg.trans_le halloc).trans hf
  refine ⟨result, ?_, ?_, PA17A19RuntimeTests010.represents_of_leading_frame full configuration capWords
    state.heap _ (by omega) hq rep bitmap hs hroom result.leading⟩
  · intro budget hbudget
    rw [result.good budget hbudget]
    have hg := PA17A19RuntimeTests010.rawGood_correct (prepareNormalization q full).indexed
      (logicalHeap q capWords state.heap) (rowBase + budget * (treeSize q full + 1))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)) counts
      (row.get ⟨budget, hbudget⟩) hi.counts (by simpa only [hsize] using hi.entries ⟨budget, hbudget⟩)
    rw [IndexedQuery.entryAt_get row budget hbudget]
    simpa only [hsize] using congrArg (fun b => BitVec.ofNat bits (bit b)) hg
  · intro budget hbudget
    rw [result.bad budget hbudget]
    have hb' := PA17A19RuntimeTests010.rawBad_correct (prepareNormalization q full).indexed
      (logicalHeap q capWords state.heap) (rowBase + budget * (treeSize q full + 1))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full))
      counts (row.get ⟨budget, hbudget⟩) node hi.counts (by simpa only [hsize] using hi.entries ⟨budget, hbudget⟩) hi.parents
    unfold IndexedQuery.budgetExtensionTest
    rw [IndexedQuery.entryAt_get row budget hbudget]
    simpa only [hsize] using congrArg (fun b => BitVec.ofNat bits (bit b)) hb'

theorem actual_tests_trace_bound {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (q size : Nat) (state : WordState bits) (ht : 0 < size) :
    (packingDynamicTrace rom containing (PA17A19RuntimeTests010.steps q size) state).length ≤ 8736 * ((q + 1) * size) := by
  exact (packingDynamicTrace_length_le rom containing _ state).trans
    ((Nat.mul_le_mul_left 12 (PA17A19RuntimeTests010.steps_bound q size ht)).trans_eq (by ring))

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSemantics019
