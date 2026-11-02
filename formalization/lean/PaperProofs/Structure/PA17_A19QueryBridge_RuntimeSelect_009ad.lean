module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ac

/-! Descent initialization really overwrites both exported slots and all
three local header caches. The leaf/current/tool words are read from this
same heap, with no preinitialized local scratch or supplied choice. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def descendInitHeap {bits : Nat} (header q size current : Nat) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update (Function.update (Function.update (Function.update (Function.update heap
    (BitVec.ofNat bits (header + 14)) (BitVec.ofNat bits (nodeSlot header q size)))
    (BitVec.ofNat bits (header + 15)) (BitVec.ofNat bits (toolSlot header q size)))
    (BitVec.ofNat bits (header + 13)) (BitVec.ofNat bits size))
    (BitVec.ofNat bits (nodeSlot header q size)) (BitVec.ofNat bits current))
    (BitVec.ofNat bits (toolSlot header q size)) (BitVec.ofNat bits 0)

theorem descendInit_result {bits : Nat} (rom : PhysicalROM) (header q size current : Nat) (state : WordState bits)
    (hroom : Fits bits (endpoint header q size)) (hh : state.register .address = BitVec.ofNat bits header)
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hc : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (childBase header q))
    (hn : state.heap (BitVec.ofNat bits (header + 1)) = BitVec.ofNat bits current) :
    let after := executeOps rom descendInit state
    after.register .address = BitVec.ofNat bits header ∧ after.heap = descendInitHeap header q size current state.heap := by
  have ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    have he := congrArg (BitVec.ofNat bits) hsize
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he
  have h1 : Fits bits 1 := (show 1 ≤ endpoint header q size by unfold endpoint; omega).trans_lt hroom
  have htool : Fits bits (toolSlot header q size) := (show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt hroom
  have he (i j : Nat) (hi : i ≤ 15) (hj : j ≤ 15) :
      BitVec.ofNat bits (header + i) = BitVec.ofNat bits (header + j) ↔ i = j := by
    rw [ofNat_injective_of_fit _ _
      ((show header + i ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt hroom)
      ((show header + j ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt hroom)]
    omega
  have hp : childBase header q + (size + 1) = nodeSlot header q size := by unfold nodeSlot; omega
  have hs : toolSlot header q size - 1 = nodeSlot header q size := by unfold toolSlot nodeSlot; omega
  have hn' : nodeSlot header q size + 1 = toolSlot header q size := by unfold toolSlot nodeSlot; omega
  simp +decide (disch := omega) only [descendInit, descendInitHeap, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, ht, hh, hc, hn, he, BitVec.ofNat_add_ofNat, hp, hs, hn',
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt htool]

theorem descendInitHeap_cells {bits : Nat} (header q size current : Nat) (heap : BitVec bits → BitVec bits)
    (hroom : Fits bits (endpoint header q size)) :
    let fresh := descendInitHeap header q size current heap
    fresh (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits size ∧
      fresh (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size) ∧
      fresh (BitVec.ofNat bits (header + 15)) = BitVec.ofNat bits (toolSlot header q size) ∧
      fresh (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits current ∧
      fresh (BitVec.ofNat bits (toolSlot header q size)) = BitVec.ofNat bits 0 := by
  have he (i j : Nat) (hi : i ≤ 15) (hj : j ≤ 15) :
      BitVec.ofNat bits (header + i) = BitVec.ofNat bits (header + j) ↔ i = j := by
    rw [ofNat_injective_of_fit _ _
      ((show header + i ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt hroom)
      ((show header + j ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt hroom)]
    omega
  have hnode (i : Nat) (hi : i ≤ 15) : BitVec.ofNat bits (header + i) ≠ BitVec.ofNat bits (nodeSlot header q size) := by
    apply (ofNat_injective_of_fit _ _
      ((show header + i ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt hroom)
      ((show nodeSlot header q size ≤ endpoint header q size by unfold nodeSlot endpoint; omega).trans_lt hroom)).not.mpr
    unfold nodeSlot childBase
    omega
  have htool (i : Nat) (hi : i ≤ 15) : BitVec.ofNat bits (header + i) ≠ BitVec.ofNat bits (toolSlot header q size) := by
    apply (ofNat_injective_of_fit _ _
      ((show header + i ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt hroom)
      ((show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt hroom)).not.mpr
    unfold toolSlot childBase
    omega
  have hnt : BitVec.ofNat bits (nodeSlot header q size) ≠ BitVec.ofNat bits (toolSlot header q size) := by
    apply (ofNat_injective_of_fit _ _
      ((show nodeSlot header q size ≤ endpoint header q size by unfold nodeSlot endpoint; omega).trans_lt hroom)
      ((show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt hroom)).not.mpr
    unfold nodeSlot toolSlot
    omega
  simp +decide (disch := omega) [descendInitHeap, Function.update_apply, he, hnode, htool]

def maskedLeaf {bits : Nat} (current : Nat) (token : BitVec bits) : BitVec bits :=
  if current = 0 then BitVec.ofNat bits 0 else token

def descendedTool {bits : Nat} (current : Nat) (token oldTool : BitVec bits) : BitVec bits :=
  if (maskedLeaf current token).toNat = 0 then oldTool else maskedLeaf current token

def descendedNode {bits : Nat} (current : Nat) (token child : BitVec bits) : BitVec bits :=
  if (maskedLeaf current token).toNat = 0 then child else BitVec.ofNat bits 0

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
