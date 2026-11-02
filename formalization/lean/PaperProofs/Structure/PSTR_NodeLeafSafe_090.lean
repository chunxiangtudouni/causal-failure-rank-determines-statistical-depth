module

public import PaperProofs.Structure.PSTR_LeafUsedAccess_089

/-! ONE actual54/87-step leaf-stage witness supplies original leafBitmap,
the whole-heap frame and every proper-clock actual fetch/decode/access. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRNodeLeafSafe

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRCountKernel

theorem actual_leaf {bits q : Nat} (whole : List PackingOp) (start : Nat) (hc : PSTRNodeLeaf.Contains whole start)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (full : List (Finset (Fin q))) (command : Command) (configuration : Configuration q)
    (capWords heapWords : Nat) (state : WordState bits) (node : (prepareNormalization q full).indexed.NodeId)
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
    (hroom : PSTRCountWorkspace.base q full capWords bits + 15 < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    ∃ steps ≤ 87,
      (let after := packingRun (callInput q full command) whole steps state
       after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (start + 87)) ∧
         after.heap = state.heap ∧ (after.register .value).toNat =
           (IndexedUsedCounts.leafBitmap (prepareNormalization q full).indexed configuration.used).get node) ∧
      (∀ clock ≤ steps, (packingRun (callInput q full command) whole clock state).heap = state.heap) ∧
      (∀ clock < steps, AtSafe (callInput q full command) whole heapWords
        (packingRun (callInput q full command) whole clock state)) := by
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
  have value := PSTRLeafCertifiedPrefix.kernel_value rom whole (start + 51)
    (PSTRNodeLeaf.leaf_bounds whole start hc) (PSTRNodeLeaf.leaf_code whole start hc)
    hwords hpcfit full configuration capWords current node hb hq hw current_rep rfl rfl
    bitmap hr hN1 hq2 ht1 hprod ready.2.1 ready.2.2.1 ready.1 current_pc current_active
  have prefixes := PSTRLeafPrefix.prepared_prefix rom whole start hc hwords hpcfit state hp ha
  let steps := 51 + PSTRLeafPrefix.duration current
  have all : ∀ clock ≤ steps, (packingRun rom whole clock state).heap = state.heap := prefixes.2.2.2
  have prepareSlice : PSTROuterCountCode.BlockAt whole start PSTRLeafPrepare.program := by
    refine ⟨by have hh := hc.bound; rw [PSTRNodeLeaf.programAt_length] at hh; rw [PSTRLeafPrepare.program_length]; omega, ?_⟩
    intro i hi
    exact (hc.code i (by rw [PSTRNodeLeaf.programAt_length]; rw [PSTRLeafPrepare.program_length] at hi; omega)).trans
      (PSTRNodeLeaf.prepare_code start i hi)
  refine ⟨steps, prefixes.1, ⟨prefixes.2.1, prefixes.2.2.1, all steps le_rfl, ?_⟩, all, ?_⟩
  · rw [PSTRWordSegments.run_add, PSTRNodeLeaf.prepare_run rom whole start hc hwords hpcfit state hp ha]
    exact value
  · intro clock hclock
    by_cases hprepare : clock < 51
    · exact PSTROuterReadAccess.prepare_safe full command configuration capWords heapWords state node whole start prepareSlice
        hwords hpcfit hb hq rep ((Nat.le_succ _).trans_lt hN1) hi hroom hp ha clock hprepare
    · change clock < 51 + PSTRLeafPrefix.duration current at hclock
      rw [show clock = 51 + (clock - 51) by omega, PSTRWordSegments.run_add,
        PSTRNodeLeaf.prepare_run rom whole start hc hwords hpcfit state hp ha]
      exact PSTRLeafUsedAccess.kernel_safe whole (start + 51)
        (PSTRNodeLeaf.leaf_bounds whole start hc) (PSTRNodeLeaf.leaf_code whole start hc)
        hwords hpcfit full command configuration capWords heapWords current node hb hq hw current_rep bitmap hr
        hN1 hq2 ht1 hprod ready.2.1 ready.1 (by omega) current_pc current_active (clock - 51) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRNodeLeafSafe
