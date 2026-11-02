module

public import Structure.PSTR_LeafBitmap_030

/-! Original leafBitmap VALUE semantics for the actual containing-program
kernel. The earlier standalone HALT theorem is not restarted as a helper:
both branches here exit ACTIVE at the next containing instruction. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLeafBitmapEmbedded

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims
open PSTRLeafUsedEmbedded

theorem actual_leaf {bits q : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start : Nat) (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (full : List (Finset (Fin q))) (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : (rom.words .input).getD 0 0 = full.length) (hQ : (rom.words .input).getD 1 0 = q)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hN1 : Fits bits (full.length + 1)) (hq2 : Fits bits (q + 2))
    (ht1 : Fits bits (treeSize q full + 1)) (hprod : Fits bits ((full.length + 1) * (q + 2)))
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.register .flag = lowMask bits (CapacityBits.width q))
    (haddress : state.register .address = BitVec.ofNat bits
      (PSTRStaticHeap.metadataAddress q capWords bits (PSTRStaticLayout.offset q full 6 + node.val)))
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    ∃ steps ≤ 36,
      let after := packingRun rom whole steps state
      after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (start + 36)) ∧
        after.heap = state.heap ∧ (after.register .value).toNat =
          (IndexedUsedCounts.leafBitmap (prepareNormalization q full).indexed configuration.used).get node := by
  have hread : state.heap (state.register .address) = BitVec.ofNat bits
      (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
        | none => 0 | some tool => tool.val + 1) := by
    rw [haddress]
    exact PSTRStaticHeap.leaf_word full configuration capWords state.heap hq rep node
  cases hl : (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
  | none =>
    have hz : (state.heap (state.register .address)).toNat = 0 := by rw [hread, hl]; rfl
    have result := actual_none rom whole start hbound hcode hwords hpcfit state hp ha hz
    refine ⟨3, by decide, result.1, result.2.1, result.2.2.1, ?_⟩
    rw [result.2.2.2]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, IndexedUsedCounts.leafBitmap, cache_get_ofFn, hl]
  | some tool =>
    have hfit : tool.val + 1 < 2 ^ bits :=
      (show tool.val + 1 ≤ q + 2 by have ht := tool.isLt; omega).trans_lt hq2
    have hlabel : (state.heap (state.register .address)).toNat = tool.val + 1 := by
      rw [hread, hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
    have hz : ¬(state.heap (state.register .address)).toNat = 0 := by rw [hlabel]; omega
    let current := executeOps rom (leadAt start ++ [PSTRLeafUsed.branch]) state
    have hv : (current.register .value).toNat = tool.val + 1 := by
      rw [prefix_value]
      exact hlabel
    have room := PSTRLeafBitmap.bitmap_room full.length (treeSize q full) capWords tool hq bitmap hr
    have hval := PSTRLeafUsedRun.body_value rom current full.length q (treeSize q full) tool.val capWords
      hb hq hw hN hQ (by rw [prefix_heap]; exact rep.1)
      (by rw [prefix_heap]; exact rep.2.2.2.1) hv
      (by rw [prefix_width]; exact hwidth) (by rw [prefix_mask]; exact hmask)
      hN1 hq2 ht1 hprod room.1 room.2.2.2 room.2.1 room.2.2.1
    have result := actual_some rom whole start hbound hcode hwords hpcfit state hp ha hz
    refine ⟨36, le_rfl, result.1, result.2.1, result.2.2, ?_⟩
    rw [positive_run rom whole start hbound hcode hwords hpcfit state hp ha hz]
    have hused := rep.2.2.2.2.2.2.2.1 tool
    have hvalue : ((executeOps rom PSTRLeafUsed.body current).register .value).toNat =
        logicalHeap q capWords state.heap (tableWords full.length q (treeSize q full) + tool.val) := by
      simpa only [show current.heap = state.heap from prefix_heap rom start state] using hval
    simpa only [IndexedUsedCounts.leafBitmap, cache_get_ofFn, hl, bit, decide_eq_true_eq] using hvalue.trans hused

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits)
    (steps : Nat) (hs : steps ≤ 36) :
    (packingDynamicTrace rom whole steps state).length ≤ 432 := by
  have ht := packingDynamicTrace_length_le rom whole steps state
  omega

end PaperProofs.Structure.LaminarTree.PSTRLeafBitmapEmbedded
