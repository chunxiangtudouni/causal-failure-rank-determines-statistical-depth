module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009at
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ap
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009au

/-! Exact tool export by the actual fixed281op selector. Canonical candidate
values are produced by the real reverse-parent kernel; actual initialization
creates tool0 and overwrites arbitrary scratch before the runtime descent. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims IndexedDescent

theorem actual_desc_selected {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size size state)
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hc : PhysicalCandidatesFor full usedCounts capacity header state.heap)
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (hn : state.heap (BitVec.ofNat bits (nodeSlot header q size)) =
      BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed node))
    (ht : state.heap (BitVec.ofNat bits (toolSlot header q size)) = BitVec.ofNat bits 0) :
    (packingRun (callInput q full command) containing (descendSteps size) state).heap (BitVec.ofNat bits (toolSlot header q size)) =
      BitVec.ofNat bits (PA17LeafLabels005.encodeTool
        (node.bind (selectAt (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed) usedCounts capacity))) := by
  let rom := callInput q full command
  let looped := packingRun rom containing (91 * size) state
  have r0 : DescReady full configuration origin capWords header base counts parents size (0 + size) state := by
    simpa only [Nat.zero_add] using ready
  have hend : DescReady full configuration origin capWords header base counts parents size 0 looped :=
    descReady_iterations em layout command configuration state r0
  rw [descendSteps, run_add, fetched_desc_test em rom looped hend.pc hend.active,
    executeOps_heap_of_no_store rom (descendTest origin) looped (descendTest_noStore origin)]
  cases node with
  | none => exact (actual_desc_stopped em layout command configuration state ready hn).trans ht
  | some node =>
    have hs : size = (prepareNormalization q full).indexed.nodes.size := by
      simpa only [treeSize, ne_of_gt layout.positive, ite_false] using layout.size_eq
    simpa only [Option.bind_some, selectAt, ← hs] using
      actual_desc_tool_node em layout command configuration state ready usedCounts capacity hc node hn ht

theorem physicalCandidates_init {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (current : Nat) (heap : BitVec bits → BitVec bits)
    (hc : PhysicalCandidatesFor full usedCounts capacity header heap) :
    PhysicalCandidatesFor full usedCounts capacity header (descendInitHeap header q size current heap) := by
  have hs : size = (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt layout.positive, ite_false] using layout.size_eq
  have hkeep (encoded : Nat) (he : encoded ≤ size) :
      descendInitHeap header q size current heap (BitVec.ofNat bits (childBase header q + encoded)) =
        heap (BitVec.ofNat bits (childBase header q + encoded)) := by
    apply descendInitHeap_frame layout current heap _ ((Nat.le_succ _).trans_lt (layout.targetFits encoded he))
    · unfold childBase
      omega
    · unfold childBase
      omega
    · unfold childBase
      omega
    · unfold nodeSlot
      omega
    · unfold toolSlot
      omega
  constructor
  · simpa only [Nat.add_zero] using (hkeep 0 (by omega)).trans hc.1
  · intro parent
    rw [hkeep (parent.val + 1) (by have hp := parent.isLt; omega)]
    exact hc.2 parent

theorem actual_core_selected {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (sources : SelectionSources full usedCounts capacity capWords base counts parents state.heap)
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (hn : state.heap (BitVec.ofNat bits (header + 1)) = BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed node)) :
    (packingRun (callInput q full command) containing (coreSteps size) state).heap (BitVec.ofNat bits (toolSlot header q size)) =
      BitVec.ofNat bits (PA17LeafLabels005.encodeTool
        (node.bind (selectAt (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed) usedCounts capacity))) := by
  let rom := callInput q full command
  let parented := packingRun rom containing (parentSteps size) state
  let initialized := packingRun rom containing 26 parented
  let encoded := encodedNode (prepareNormalization q full).indexed node
  have hs : size = (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt layout.positive, ite_false] using layout.size_eq
  have hb : encoded ≤ size := by
    have hh := UniformNormalizationRAM.encodedNode_le (prepareNormalization q full).indexed node
    omega
  have hfit : Fits bits encoded := hb.trans_lt layout.sizeFits
  have hp := actual_parent_kernel (core_parent_embedded em) layout command configuration row budget state
    data.represents data.width data.mask data.parentBound data.counts_eq data.parents_eq data.base_eq data.budgetBound
    data.rowWord data.selectedWord data.address data.pc data.active
  have hc := actual_parent_candidateBounded (core_parent_embedded em) layout command configuration state data
  have hcanonical := actual_parent_candidates_canonical (core_parent_embedded em) layout command configuration state data usedCounts capacity sources
  have hparentNode : parented.heap (BitVec.ofNat bits (header + 1)) = BitVec.ofNat bits encoded := by
    rw [actual_parent_frame (core_parent_embedded em) layout command configuration state data (parentSteps size) le_rfl
      (header + 1) (layout.headerFits 1 (by decide)) (.inl (by omega))]
    exact hn
  have hbound : (parented.heap (BitVec.ofNat bits (header + 1))).toNat ≤ size := by
    rw [hparentNode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
    exact hb
  have hi := execute_desc_initial_ready layout command configuration parented hp.2.2.2.2 hc hbound hp.2.2.1 hp.2.1 hp.1
  have hinit : initialized = executeOps (callInput q full command) descendInit parented := fetched_core_init em rom parented hp.2.1 hp.1
  have hr : DescReady full configuration (origin + 190) capWords header base counts parents size size initialized := by
    rw [hinit]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hi.1
  have ht : initialized.heap (BitVec.ofNat bits (toolSlot header q size)) = BitVec.ofNat bits 0 := by
    rw [hinit]
    exact hi.2
  have hh := descendInit_result rom header q size encoded parented layout.endpointFits hp.2.2.1
    (hp.2.2.2.2.represents.1.trans layout.size_eq.symm) hp.2.2.2.2.candidates hparentNode
  have hheap : initialized.heap = descendInitHeap header q size encoded parented.heap := by
    rw [hinit]
    exact hh.2
  have hnode : initialized.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits encoded := by
    rw [hheap]
    exact (descendInitHeap_cells header q size encoded parented.heap layout.endpointFits).2.2.2.1
  have hca : PhysicalCandidatesFor full usedCounts capacity header initialized.heap := by
    rw [hheap]
    exact physicalCandidates_init layout usedCounts capacity encoded parented.heap hcanonical
  rw [coreSteps, run_add, run_add]
  exact actual_desc_selected (core_desc_embedded em) layout command configuration initialized hr usedCounts capacity hca node hnode ht

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
