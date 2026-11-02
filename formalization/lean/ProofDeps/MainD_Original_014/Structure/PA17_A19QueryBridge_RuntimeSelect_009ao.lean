module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009am

/-! Concrete real descent-tail prefix frame/access. Only cached addresses
produced by this run and finite node bounds are required; arbitrary tools,
counts and capacity payload values remain unrestricted. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem ReverseLayout.header_node_ne {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (offset : Nat) (ho : offset ≤ 15) :
    BitVec.ofNat bits (header + offset) ≠ BitVec.ofNat bits (nodeSlot header q size) := by
  apply (ofNat_injective_of_fit _ _ (layout.headerFits offset ho)
    ((show nodeSlot header q size ≤ endpoint header q size by unfold nodeSlot endpoint; omega).trans_lt layout.endpointFits)).not.mpr
  unfold nodeSlot childBase
  omega

theorem ReverseLayout.header_tool_ne {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (offset : Nat) (ho : offset ≤ 15) :
    BitVec.ofNat bits (header + offset) ≠ BitVec.ofNat bits (toolSlot header q size) := by
  apply (ofNat_injective_of_fit _ _ (layout.headerFits offset ho)
    ((show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt layout.endpointFits)).not.mpr
  unfold toolSlot childBase
  omega

theorem WordPrefixFrame.of_step {bits : Nat} (rom : PhysicalROM) (code : List PackingOp)
    (state : WordState bits) (address : BitVec bits)
    (hstep : ∀ clock (hc : clock < code.length),
      (packingExecuteOp rom code[clock] (executeOps rom (code.take clock) state)).heap address =
        (executeOps rom (code.take clock) state).heap address) : WordPrefixFrame rom code state address := by
  intro clock hc
  induction clock with
  | zero => rfl
  | succ clock ih =>
    have hcl : clock < code.length := by omega
    rw [List.take_succ_eq_append_getElem hcl, executeOps_append]
    exact (hstep clock hcl).trans (ih (by omega))

theorem descendTail_prefixFrame {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (rom : PhysicalROM) (origin : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hnodePtr : state.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size))
    (htoolPtr : state.heap (BitVec.ofNat bits (header + 15)) = BitVec.ofNat bits (toolSlot header q size))
    (address : BitVec bits) (hn : address ≠ BitVec.ofNat bits (nodeSlot header q size))
    (ht : address ≠ BitVec.ofNat bits (toolSlot header q size)) (hf : address ≠ BitVec.ofNat bits (header + 13)) :
    WordPrefixFrame rom (descendTail origin) state address := by
  have hHN := layout.header_node_ne
  have hHT := layout.header_tool_ne
  apply WordPrefixFrame.of_step
  intro clock hc
  by_cases hs : clock = 11 ∨ clock = 22 ∨ clock = 28
  · rcases hs with rfl | rfl | rfl
    · have hi : (executeOps rom ((descendTail origin).take 11) state).register .index = BitVec.ofNat bits (toolSlot header q size) := by
        simp +decide only [descendTail, descendTailLead, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
          executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte, hh, htoolPtr, BitVec.ofNat_add_ofNat]
      change Function.update _ ((executeOps rom ((descendTail origin).take 11) state).register .index) _ address = _
      rw [hi, Function.update_of_ne ht]
    · have hi : (executeOps rom ((descendTail origin).take 22) state).register .index = BitVec.ofNat bits (nodeSlot header q size) := by
        simp +decide (disch := omega) only [descendTail, descendTailLead, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
          executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte, hh, hnodePtr, htoolPtr, hHT, BitVec.ofNat_add_ofNat]
      change Function.update _ ((executeOps rom ((descendTail origin).take 22) state).register .index) _ address = _
      rw [hi, Function.update_of_ne hn]
    · have hi : (executeOps rom ((descendTail origin).take 28) state).register .index = BitVec.ofNat bits (header + 13) := by
        simp +decide only [descendTail, descendTailLead, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
          executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte, hh, BitVec.ofNat_add_ofNat]
      change Function.update _ ((executeOps rom ((descendTail origin).take 28) state).register .index) _ address = _
      rw [hi, Function.update_of_ne hf]
  · have hn : HeapPreservingOp (descendTail origin)[clock] := by
      change clock < 32 at hc
      interval_cases clock <;> simp_all [descendTail, descendTailLead, HeapPreservingOp]
    exact congrFun (PA17A19RuntimeRanks008.preserving_step_heap rom (descendTail origin)[clock] _ hn) address

theorem descendTail_access {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (rom : PhysicalROM) (origin current : Nat) (hcurrent : current ≤ size) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hnodePtr : state.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size))
    (htoolPtr : state.heap (BitVec.ofNat bits (header + 15)) = BitVec.ofNat bits (toolSlot header q size))
    (hbase : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (childBase header q))
    (hnode : state.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits current)
    (clock : Nat) (hc : clock < (descendTail origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((descendTail origin).take clock) state) (descendTail origin)[clock] := by
  have hHN := layout.header_node_ne
  have hHT := layout.header_tool_ne
  have hroom := layout.allocated
  change clock < 32 at hc
  interval_cases clock <;> try exact True.intro
  all_goals simp +decide (disch := omega) only [descendTail, descendTailLead, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero,
    executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    hh, hnodePtr, htoolPtr, hbase, hnode, hHN, hHT, BitVec.ofNat_add_ofNat,
    packingAccessFits, AccessFits, BitVec.toNat_ofNat]
  all_goals exact (Nat.mod_le _ _).trans_lt (by unfold nodeSlot toolSlot endpoint childBase at *; omega)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
