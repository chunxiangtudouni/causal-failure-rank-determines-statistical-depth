module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009ah

/-! A complete real91op descent round: the leaf label is actually fetched
from original metadata, then the real node/tool/fuel stores are executed.
Node0 uses the valid canonical node0 label and masks it before selection. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def clampedNode {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (current : Nat) (hcurrent : current ≤ size) : (prepareNormalization q full).indexed.NodeId :=
  ⟨current - 1, by
    have hp := layout.sizePositive
    have he : size = (prepareNormalization q full).indexed.nodes.size := by
      simpa only [treeSize, ne_of_gt layout.positive, ite_false] using layout.size_eq
    omega⟩

theorem actual_desc_round {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size (remaining + 1) state) :
    let current := (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat
    let node := clampedNode layout current ready.nodeBound
    let token := BitVec.ofNat bits
      (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
        | none => 0 | some tool => tool.val + 1)
    let oldTool := state.heap (BitVec.ofNat bits (toolSlot header q size))
    let child := state.heap (BitVec.ofNat bits (childBase header q + current))
    let after := packingRun (callInput q full command) containing 91 state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * origin) ∧
      after.register .address = BitVec.ofNat bits header ∧
      after.register .value = descendedTool current token oldTool ∧
      after.heap = descendTailHeap header q size remaining (descendedTool current token oldTool)
        (descendedNode current token child) state.heap := by
  let rom := callInput q full command
  let current := (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat
  let node := clampedNode layout current ready.nodeBound
  let token := BitVec.ofNat bits
    (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
      | none => 0 | some tool => tool.val + 1)
  let tested := executeOps rom (descendTest origin) state
  let indexed := executeOps rom descendIndex tested
  let labeled := executeOps rom leafReadProgram indexed
  have hf : Fits bits (remaining + 1) := ready.bound.trans_lt layout.sizeFits
  have hc : Fits bits current := ready.nodeBound.trans_lt layout.sizeFits
  have hnWord : state.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits current := by
    simp only [current, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have ht := descendTest_result rom origin header (remaining + 1) state hf ready.address ready.pc ready.fuel
  have hp : tested.pc = BitVec.ofNat bits (5 * (origin + 5)) := by
    simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
  have ha : tested.halted = false := by rw [executeOps_halted, ready.active]
  have hi := descendIndex_result rom header (nodeSlot header q size) current tested layout.oneFits hc ht.2.1
    (by rw [ht.2.2]; exact ready.nodePointer) (by rw [ht.2.2]; exact hnWord)
  have him : indexed.heap = state.heap := hi.2.2.trans ht.2.2
  have hirep : HeapRepresents q full capWords configuration indexed.heap := by rw [him]; exact ready.data.represents
  have hl := execute_leafRead full command configuration capWords indexed node layout.bits8 layout.positive hirep layout.lengthFits hi.1
  rcases hl with ⟨hlad, hlvalue, _, hlheap, _⟩
  have hlh : labeled.heap = state.heap := hlheap.trans him
  have hla : labeled.register .address = BitVec.ofNat bits header := by simpa only [← layout.header_eq] using hlad
  have tail := descendTail_result rom origin header q size current remaining token
    (state.heap (BitVec.ofNat bits (toolSlot header q size))) (state.heap (BitVec.ofNat bits (childBase header q + current)))
    labeled layout.endpointFits ready.nodeBound hf hla hlvalue
    (by rw [hlh]; exact ready.nodePointer) (by rw [hlh]; exact ready.toolPointer)
    (by rw [hlh]; exact ready.data.candidates) (by rw [hlh]; exact ready.fuel)
    (by rw [hlh]; exact hnWord) (by rw [hlh]) (by rw [hlh])
  rw [hlh] at tail
  have hrun : packingRun rom containing 91 state = executeOps rom (descendTail origin) labeled := by
    rw [show 91 = 5 + 86 from rfl, run_add, fetched_desc_test em rom state ready.pc ready.active,
      fetched_desc_body em rom tested hp ha, descendBody_eq, executeOps_append, executeOps_append]
  dsimp only
  rw [hrun]
  refine ⟨?_, tail.2.2.2.2.1, tail.1, tail.2.1, tail.2.2.2.2.2⟩
  rw [executeOps_halted, executeOps_halted, executeOps_halted, executeOps_halted, ready.active]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
