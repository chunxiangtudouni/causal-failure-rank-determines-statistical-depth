module

public import Structure.PSTR_LeafUsedEmbedded_029
public import Structure.PSTR_HD_StaticHeap_020
public import PaperProofs.Structure.IndexedUsedCounts

/-! Derive the leaf bitmap from ORIGINAL HeapRepresents by actual cached
label loading and actual packed used-bit reading. The old IndexedUsedCounts
leafBitmap is a correctness specification here, never a supplied ROM field. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLeafBitmap

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem bitmap_room {bits q : Nat} (N t capWords : Nat) (tool : Fin q) (hq : 0 < q)
    (bitmap : tableWords N q t + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q)) :
    Fits bits (tableWords N q t + tool.val) ∧
    Fits bits ((tableWords N q t + tool.val) * CapacityBits.width q) ∧
    Fits bits (4 + (tableWords N q t + tool.val) * CapacityBits.width q / bits + 1) ∧
    tableWords N q t + tool.val < capWords := by
  have ha : tableWords N q t + tool.val < capWords := by have ht := tool.isLt; omega
  have hw : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hs : (tableWords N q t + tool.val) * CapacityBits.width q < capWords * CapacityBits.width q :=
    Nat.mul_lt_mul_of_pos_right ha hw
  have hscalar : Fits bits ((tableWords N q t + tool.val) * CapacityBits.width q) :=
    hs.trans ((Nat.le_add_left (capWords * CapacityBits.width q) 4).trans_lt hr)
  have haddr : Fits bits (tableWords N q t + tool.val) :=
    (show tableWords N q t + tool.val ≤ (tableWords N q t + tool.val) * CapacityBits.width q by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (tableWords N q t + tool.val) (show 1 ≤ CapacityBits.width q by omega)).trans_lt hscalar
  have hd := Nat.div_le_self ((tableWords N q t + tool.val) * CapacityBits.width q) bits
  have hn : Fits bits (4 + (tableWords N q t + tool.val) * CapacityBits.width q / bits + 1) :=
    (show 4 + (tableWords N q t + tool.val) * CapacityBits.width q / bits + 1 ≤
      4 + capWords * CapacityBits.width q by omega).trans_lt hr
  exact ⟨haddr, hscalar, hn, ha⟩

theorem actual_leaf {bits q : Nat} (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
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
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    ∃ steps ≤ 37,
      let after := packingRun rom PSTRLeafUsed.program steps state
      after.halted = true ∧ after.heap = state.heap ∧
      (after.register .value).toNat =
        (IndexedUsedCounts.leafBitmap (prepareNormalization q full).indexed configuration.used).get node := by
  have hread : state.heap (state.register .address) = BitVec.ofNat bits
      (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
        | none => 0 | some tool => tool.val + 1) := by
    rw [haddress]
    exact PSTRStaticHeap.leaf_word full configuration capWords state.heap hq rep node
  cases hl : (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
  | none =>
    have hz : (state.heap (state.register .address)).toNat = 0 := by
      rw [hread, hl]
      rfl
    have result := PSTRLeafUsedRun.actual_none rom state hb hp ha hz
    dsimp only at result
    refine ⟨4, by decide, result.1, result.2.1, ?_⟩
    rw [result.2.2]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, IndexedUsedCounts.leafBitmap, cache_get_ofFn, hl]
  | some tool =>
    have hfit : tool.val + 1 < 2 ^ bits := (show tool.val + 1 ≤ q + 2 by have ht := tool.isLt; omega).trans_lt hq2
    have hlabel : (state.heap (state.register .address)).toNat = tool.val + 1 := by
      rw [hread, hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
    have room := bitmap_room full.length (treeSize q full) capWords tool hq bitmap hr
    have result := PSTRLeafUsedRun.actual_some rom state full.length q (treeSize q full) tool.val capWords
      hb hq hw hN hQ rep.1 rep.2.2.2.1 hlabel hwidth hmask hN1 hq2 ht1 hprod
      room.1 room.2.2.2 room.2.1 room.2.2.1 hp ha
    dsimp only at result
    refine ⟨37, le_rfl, result.1, result.2.1, ?_⟩
    have hused := rep.2.2.2.2.2.2.2.1 tool
    have hvalue := result.2.2.trans hused
    simpa only [IndexedUsedCounts.leafBitmap, cache_get_ofFn, hl, bit, decide_eq_true_eq] using hvalue

end PaperProofs.Structure.LaminarTree.PSTRLeafBitmap
