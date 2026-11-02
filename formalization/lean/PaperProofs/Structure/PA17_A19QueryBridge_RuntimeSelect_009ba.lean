module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009az

/-! One consumable certificate for the fixed selector, with all scratch and
runtime loop invariants eliminated by its own actual code. The remaining
sources describe same-call materialization, never a candidate/tool answer. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims IndexedDescent

theorem materialized_node_bound {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (heap : BitVec bits → BitVec bits) (node : Option (prepareNormalization q full).indexed.NodeId)
    (hn : heap (BitVec.ofNat bits (header + 1)) = BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed node)) :
    (heap (BitVec.ofNat bits (header + 1))).toNat ≤ size := by
  have hs : size = (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt layout.positive, ite_false] using layout.size_eq
  have hb : encodedNode (prepareNormalization q full).indexed node ≤ size := by
    have hh := UniformNormalizationRAM.encodedNode_le (prepareNormalization q full).indexed node
    omega
  rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb.trans_lt layout.sizeFits)]
  exact hb

theorem actual_selector {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (sources : SelectionSources full usedCounts capacity capWords base counts parents state.heap)
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (hn : state.heap (BitVec.ofNat bits (header + 1)) = BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed node)) :
    let after := packingRun (callInput q full command) containing (coreSteps size) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 281)) ∧
      after.register .address = BitVec.ofNat bits header ∧
      after.heap (BitVec.ofNat bits (toolSlot header q size)) =
        BitVec.ofNat bits (PA17LeafLabels005.encodeTool
          (node.bind (selectAt (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed) usedCounts capacity))) ∧
      (∀ clock < coreSteps size, DecodedAt (callInput q full command) containing heapWords
        (packingRun (callInput q full command) containing clock state)) ∧
      (∀ clock ≤ coreSteps size, ∀ physical, Fits bits physical →
        (physical < header + 8 ∨ endpoint header q size ≤ physical) →
        (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) =
          state.heap (BitVec.ofNat bits physical)) ∧
      (∀ clock ≤ coreSteps size, HeapRepresents q full capWords configuration
        (packingRun (callInput q full command) containing clock state).heap) ∧
      (packingDynamicTrace (callInput q full command) containing (coreSteps size) state).length ≤ 3600 * (size + 1) := by
  have hb := materialized_node_bound layout state.heap node hn
  have hc := actual_core_kernel em layout command configuration state data hb
  refine ⟨hc.1, hc.2.1, hc.2.2.1, actual_core_selected em layout command configuration state data usedCounts capacity sources node hn,
    ?_, ?_, ?_, actual_core_trace _ containing size state⟩
  · exact actual_core_decoded em layout command configuration state data hb
  · exact actual_core_prefixFrame em layout command configuration state data hb
  · exact actual_core_represents em layout command configuration state data hb

theorem actual_selector_code_trace_cost {bits : Nat} (rom : PhysicalROM) (origin : Nat)
    (containing : List PackingOp) (size : Nat) (state : WordState bits) :
    (packingCode (selectionCoreAt origin)).length + (packingDynamicTrace rom containing (coreSteps size) state).length ≤
      8192 * (size + 1) := by
  have ht := actual_core_trace rom containing size state
  rw [packingCode_length, selectionCoreAt_length]
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
