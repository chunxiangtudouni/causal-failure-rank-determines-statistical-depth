module

public import Structure.PSTR_LeafPrefix_068

/-! The original leafBitmap value and EVERY actual prefix are certified
at ONE and the same data-dependent duration. This prevents existential
final-value and unrelated-prefix witnesses from being combined unsoundly. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLeafCertifiedPrefix

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRLeafUsedEmbedded

theorem kernel_value {bits q : Nat} (rom : PhysicalROM) (whole : List PackingOp)
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
    ((packingRun rom whole (PSTRLeafPrefix.duration state) state).register .value).toNat =
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
    rw [PSTRLeafPrefix.duration, ite_eq_left hz, result.2.2.2]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, IndexedUsedCounts.leafBitmap, cache_get_ofFn, hl]
  | some tool =>
    have hfit : tool.val + 1 < 2 ^ bits :=
      (show tool.val + 1 ≤ q + 2 by have ht := tool.isLt; omega).trans_lt hq2
    have hlabel : (state.heap (state.register .address)).toNat = tool.val + 1 := by
      rw [hread, hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
    have hz : ¬(state.heap (state.register .address)).toNat = 0 := by rw [hlabel]; omega
    let current := executeOps rom (leadAt start ++ [PSTRLeafUsed.branch]) state
    have hv : (current.register .value).toNat = tool.val + 1 := by rw [prefix_value]; exact hlabel
    have room := PSTRLeafBitmap.bitmap_room full.length (treeSize q full) capWords tool hq bitmap hr
    have hval := PSTRLeafUsedRun.body_value rom current full.length q (treeSize q full) tool.val capWords
      hb hq hw hN hQ (by rw [prefix_heap]; exact rep.1)
      (by rw [prefix_heap]; exact rep.2.2.2.1) hv
      (by rw [prefix_width]; exact hwidth) (by rw [prefix_mask]; exact hmask)
      hN1 hq2 ht1 hprod room.1 room.2.2.2 room.2.1 room.2.2.1
    rw [PSTRLeafPrefix.duration, ite_eq_right hz,
      positive_run rom whole start hbound hcode hwords hpcfit state hp ha hz]
    have hvalue : ((executeOps rom PSTRLeafUsed.body current).register .value).toNat =
        logicalHeap q capWords state.heap (tableWords full.length q (treeSize q full) + tool.val) := by
      simpa only [show current.heap = state.heap from prefix_heap rom start state] using hval
    simpa only [IndexedUsedCounts.leafBitmap, cache_get_ofFn, hl, bit, decide_eq_true_eq] using
      hvalue.trans (rep.2.2.2.2.2.2.2.1 tool)

theorem actual_leaf {bits q : Nat} (whole : List PackingOp) (start : Nat) (hc : PSTRNodeLeaf.Contains whole start)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (full : List (Finset (Fin q))) (command : Command) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (node : (prepareNormalization q full).indexed.NodeId)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hN1 : Fits bits (full.length + 1)) (hq2 : Fits bits (q + 2))
    (ht1 : Fits bits (treeSize q full + 1)) (hprod : Fits bits ((full.length + 1) * (q + 2)))
    (hi : state.register .index = BitVec.ofNat bits node.val)
    (savedWidth : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (savedMask : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    ∃ steps ≤ 87,
      let after := packingRun (callInput q full command) whole steps state
      after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (start + 87)) ∧
        after.heap = state.heap ∧ (after.register .value).toNat =
          (IndexedUsedCounts.leafBitmap (prepareNormalization q full).indexed configuration.used).get node ∧
        ∀ clock ≤ steps, (packingRun (callInput q full command) whole clock state).heap = state.heap := by
  let rom := callInput q full command
  let current := executeOps rom PSTRLeafPrepare.program state
  have ready := PSTRLeafPrepare.execute_ready full command configuration capWords state node hb hq rep
    ((Nat.le_succ _).trans_lt hN1) hi savedWidth savedMask
  have current_rep : HeapRepresents q full capWords configuration current.heap := by rw [ready.2.2.2.2]; exact rep
  have current_pc : current.pc = BitVec.ofNat bits (5 * (start + 51)) := by
    rw [executeOps_pc rom _ state PSTRLeafPrepare.program_straight, hp,
      PSTRLeafPrepare.program_length, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat bits) (by omega)
  have current_active : current.halted = false := by rw [executeOps_halted, ha]
  have value := kernel_value rom whole (start + 51)
    (PSTRNodeLeaf.leaf_bounds whole start hc) (PSTRNodeLeaf.leaf_code whole start hc)
    hwords hpcfit full configuration capWords current node hb hq hw current_rep rfl rfl
    bitmap hr hN1 hq2 ht1 hprod ready.2.1 ready.2.2.1 ready.1 current_pc current_active
  have prefixes := PSTRLeafPrefix.prepared_prefix rom whole start hc hwords hpcfit state hp ha
  let steps := 51 + PSTRLeafPrefix.duration current
  have all : ∀ clock ≤ steps, (packingRun rom whole clock state).heap = state.heap := prefixes.2.2.2
  refine ⟨steps, prefixes.1, prefixes.2.1, prefixes.2.2.1, all steps le_rfl, ?_, all⟩
  rw [PSTRWordSegments.run_add, PSTRNodeLeaf.prepare_run rom whole start hc hwords hpcfit state hp ha]
  exact value

end PaperProofs.Structure.LaminarTree.PSTRLeafCertifiedPrefix
