module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009am

/-! Every literal26-op descent-init prefix has true bounded access and
preserves arbitrary Word cells outside its five actual stores. H1 is
unrestricted: its value is stored as data and never used as an address here. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelectInit024

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PA17A19RuntimeSelect009

theorem prefix_frame {bits : Nat} (rom : PhysicalROM) (header q size : Nat) (state : WordState bits)
    (hroom : Fits bits (endpoint header q size))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hc : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (childBase header q))
    (address : BitVec bits)
    (h13 : address ≠ BitVec.ofNat bits (header + 13))
    (h14 : address ≠ BitVec.ofNat bits (header + 14))
    (h15 : address ≠ BitVec.ofNat bits (header + 15))
    (hn : address ≠ BitVec.ofNat bits (nodeSlot header q size))
    (ht : address ≠ BitVec.ofNat bits (toolSlot header q size))
    (count : Nat) (hcount : count ≤ 26) :
    (executeOps rom (descendInit.take count) state).heap address = state.heap address := by
  have hsizeWord : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg (BitVec.ofNat bits) hsize
  have h1 : Fits bits 1 := (show 1 ≤ endpoint header q size by unfold endpoint; omega).trans_lt hroom
  have htool : Fits bits (toolSlot header q size) :=
    (show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt hroom
  have hp : childBase header q + (size + 1) = nodeSlot header q size := by unfold nodeSlot; omega
  have hs : toolSlot header q size - 1 = nodeSlot header q size := by unfold toolSlot nodeSlot; omega
  have ha : nodeSlot header q size + 1 = toolSlot header q size := by unfold toolSlot nodeSlot; omega
  interval_cases count <;>
    simp +decide [descendInit, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hh, hsizeWord, hc, BitVec.ofNat_add_ofNat, hp, hs, ha, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt htool, Function.update_apply, h13, h14, h15, hn, ht]

theorem access_prefix {bits : Nat} (rom : PhysicalROM) (header q size heapWords : Nat) (state : WordState bits)
    (hroom : Fits bits (endpoint header q size)) (halloc : endpoint header q size ≤ heapWords)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hc : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (childBase header q))
    (count : Nat) (hcount : count < descendInit.length) :
    packingAccessFits rom heapWords (executeOps rom (descendInit.take count) state) descendInit[count] := by
  have hsizeWord : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg (BitVec.ofNat bits) hsize
  have h1 : Fits bits 1 := (show 1 ≤ endpoint header q size by unfold endpoint; omega).trans_lt hroom
  have htool : Fits bits (toolSlot header q size) :=
    (show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt hroom
  have hp : childBase header q + (size + 1) = nodeSlot header q size := by unfold nodeSlot; omega
  have hs : toolSlot header q size - 1 = nodeSlot header q size := by unfold toolSlot nodeSlot; omega
  have ha : nodeSlot header q size + 1 = toolSlot header q size := by unfold toolSlot nodeSlot; omega
  change count < 26 at hcount
  interval_cases count <;> try exact True.intro
  all_goals simp +decide [descendInit, executeOps, packingExecuteOp, wordOp, wordInstruction,
    packingAccessFits, AccessFits, hh, hsizeWord, hc, BitVec.ofNat_add_ofNat, hp, hs, ha,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt htool]
  all_goals try apply (Nat.mod_le _ _).trans_lt
  all_goals simp only [endpoint, toolSlot, nodeSlot, childBase] at halloc ⊢
  all_goals omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelectInit024
