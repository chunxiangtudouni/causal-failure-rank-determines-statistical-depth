module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ad

/-! Exact fixed32op descent continuation. The actual leaf token is masked
when current node is0; a found tool is retained, the true candidate pointer
is followed, and the physical fuel counter is decremented before backjump. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def descendTailHeap {bits : Nat} (header q size remaining : Nat) (tool node : BitVec bits)
    (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update (Function.update (Function.update heap (BitVec.ofNat bits (toolSlot header q size)) tool)
    (BitVec.ofNat bits (nodeSlot header q size)) node) (BitVec.ofNat bits (header + 13)) (BitVec.ofNat bits remaining)

theorem descendTail_result {bits : Nat} (rom : PhysicalROM) (origin header q size current remaining : Nat)
    (token oldTool child : BitVec bits) (state : WordState bits)
    (hroom : Fits bits (endpoint header q size)) (hcurrent : current ≤ size) (hr : Fits bits (remaining + 1))
    (hh : state.register .address = BitVec.ofNat bits header) (hv : state.register .value = token)
    (hnodePtr : state.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size))
    (htoolPtr : state.heap (BitVec.ofNat bits (header + 15)) = BitVec.ofNat bits (toolSlot header q size))
    (hbase : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (childBase header q))
    (hf : state.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits (remaining + 1))
    (hnode : state.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits current)
    (htool : state.heap (BitVec.ofNat bits (toolSlot header q size)) = oldTool)
    (hchild : state.heap (BitVec.ofNat bits (childBase header q + current)) = child) :
    let after := executeOps rom (descendTail origin) state
    after.register .address = BitVec.ofNat bits header ∧
      after.register .value = descendedTool current token oldTool ∧
      after.register .total = BitVec.ofNat bits remaining ∧ after.register .flag = BitVec.ofNat bits 0 ∧
      after.pc = BitVec.ofNat bits (5 * origin) ∧
      after.heap = descendTailHeap header q size remaining (descendedTool current token oldTool)
        (descendedNode current token child) state.heap := by
  have h1 : Fits bits 1 := (show 1 ≤ endpoint header q size by unfold endpoint; omega).trans_lt hroom
  have hc : Fits bits current := (show current ≤ endpoint header q size by unfold endpoint; omega).trans_lt hroom
  have hHN (i : Nat) (hi : i ≤ 15) : BitVec.ofNat bits (header + i) ≠ BitVec.ofNat bits (nodeSlot header q size) := by
    apply (ofNat_injective_of_fit _ _
      ((show header + i ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt hroom)
      ((show nodeSlot header q size ≤ endpoint header q size by unfold nodeSlot endpoint; omega).trans_lt hroom)).not.mpr
    unfold nodeSlot childBase
    omega
  have hHT (i : Nat) (hi : i ≤ 15) : BitVec.ofNat bits (header + i) ≠ BitVec.ofNat bits (toolSlot header q size) := by
    apply (ofNat_injective_of_fit _ _
      ((show header + i ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt hroom)
      ((show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt hroom)).not.mpr
    unfold toolSlot childBase
    omega
  have hCT : BitVec.ofNat bits (childBase header q + current) ≠ BitVec.ofNat bits (toolSlot header q size) := by
    apply (ofNat_injective_of_fit _ _
      ((show childBase header q + current ≤ endpoint header q size by unfold endpoint; omega).trans_lt hroom)
      ((show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt hroom)).not.mpr
    unfold toolSlot
    omega
  simp +decide (disch := omega) only
      [descendTail, descendTailLead, descendTailHeap, descendedTool, descendedNode, maskedLeaf,
       executeOps_append, executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
       hh, hv, hnodePtr, htoolPtr, hbase, hf, hnode, htool, hchild, hHN, hHT, hCT,
       BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hr,
       Nat.zero_mod, Nat.add_sub_cancel]
  exact ⟨trivial, rfl, trivial, trivial, trivial, rfl⟩

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
