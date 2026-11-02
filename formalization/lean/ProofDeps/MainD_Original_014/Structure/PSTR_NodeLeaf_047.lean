module

public import Structure.PSTR_LeafPrepare_046
public import Structure.PSTR_LeafBitmapEmbedded_044

/-! A fixed runtime leaf stage for the outer count traversal. The caller's
node is an ordinary loop register. All source addressing and width/mask
restoration are actual preceding instructions in this SAME containing run. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRNodeLeaf

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM

def programAt (start : Nat) : List PackingOp :=
  PSTRLeafPrepare.program ++ PSTRLeafUsedEmbedded.kernel (start + 51)

theorem programAt_length (start : Nat) : (programAt start).length = 87 := rfl

structure Contains (whole : List PackingOp) (start : Nat) : Prop where
  bound : start + (programAt start).length ≤ whole.length
  code : ∀ i (hi : i < (programAt start).length), whole[start + i]'(by omega) = (programAt start)[i]

theorem prepare_code (start i : Nat) (hi : i < PSTRLeafPrepare.program.length) :
    (programAt start)[i]'(by rw [programAt_length]; rw [PSTRLeafPrepare.program_length] at hi; omega) =
      PSTRLeafPrepare.program[i] := by
  change (PSTRLeafPrepare.program ++ PSTRLeafUsedEmbedded.kernel (start + 51))[i]'(by
    rw [List.length_append, PSTRLeafPrepare.program_length, PSTRLeafUsedEmbedded.kernel_length]
    rw [PSTRLeafPrepare.program_length] at hi
    omega) = _
  exact List.getElem_append_left hi

theorem leaf_bounds (whole : List PackingOp) (start : Nat) (hc : Contains whole start) :
    start + 51 + (PSTRLeafUsedEmbedded.kernel (start + 51)).length ≤ whole.length := by
  have h := hc.bound
  rw [programAt_length] at h
  rw [PSTRLeafUsedEmbedded.kernel_length]
  omega

theorem leaf_code (whole : List PackingOp) (start : Nat) (hc : Contains whole start)
    (i : Nat) (hi : i < (PSTRLeafUsedEmbedded.kernel (start + 51)).length) :
    whole[start + 51 + i]'(by
      have hh := leaf_bounds whole start hc
      omega) = (PSTRLeafUsedEmbedded.kernel (start + 51))[i] := by
  have hh := hc.code (51 + i) (by
    rw [programAt_length, PSTRLeafUsedEmbedded.kernel_length] at *
    omega)
  have hget : (programAt start)[51 + i]'(by
      rw [programAt_length, PSTRLeafUsedEmbedded.kernel_length] at *
      omega) = (PSTRLeafUsedEmbedded.kernel (start + 51))[i] := by
    change (PSTRLeafPrepare.program ++ PSTRLeafUsedEmbedded.kernel (start + 51))[51 + i]'(by
      rw [List.length_append, PSTRLeafPrepare.program_length, PSTRLeafUsedEmbedded.kernel_length]
      rw [PSTRLeafUsedEmbedded.kernel_length] at hi
      omega) = _
    rw [List.getElem_append_right (by rw [PSTRLeafPrepare.program_length]; omega)]
    simp only [PSTRLeafPrepare.program_length, Nat.add_sub_cancel_left]
  simpa only [Nat.add_assoc] using hh.trans hget

theorem prepare_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 51 state = executeOps rom PSTRLeafPrepare.program state := by
  apply PSTRLeafPrepare.containing_run rom whole start ?_ ?_ hw hpcfit state hp ha
  · have h := hc.bound
    rw [programAt_length] at h
    rw [PSTRLeafPrepare.program_length]
    omega
  · intro i hi
    exact (hc.code i (by rw [programAt_length]; rw [PSTRLeafPrepare.program_length] at hi; omega)).trans
      (prepare_code start i hi)

theorem actual_leaf {bits q : Nat} (whole : List PackingOp) (start : Nat) (hc : Contains whole start)
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
          (IndexedUsedCounts.leafBitmap (prepareNormalization q full).indexed configuration.used).get node := by
  let rom := callInput q full command
  let current := executeOps rom PSTRLeafPrepare.program state
  have ready := PSTRLeafPrepare.execute_ready full command configuration capWords state node hb hq rep
    ((Nat.le_succ _).trans_lt hN1) hi savedWidth savedMask
  have current_rep : HeapRepresents q full capWords configuration current.heap := by rw [ready.2.2.2.2]; exact rep
  have current_pc : current.pc = BitVec.ofNat bits (5 * (start + 51)) := by
    rw [executeOps_pc rom PSTRLeafPrepare.program state PSTRLeafPrepare.program_straight, hp,
      PSTRLeafPrepare.program_length, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat bits) (show 5 * start + 5 * 51 = 5 * (start + 51) by omega)
  have current_active : current.halted = false := by rw [executeOps_halted, ha]
  obtain ⟨steps, hsteps, result⟩ := PSTRLeafBitmapEmbedded.actual_leaf rom whole (start + 51)
    (leaf_bounds whole start hc) (leaf_code whole start hc) hwords hpcfit full configuration capWords current node
    hb hq hw current_rep (by rfl) (by rfl) bitmap hr hN1 hq2 ht1 hprod
    ready.2.1 ready.2.2.1 ready.1 current_pc current_active
  refine ⟨51 + steps, by omega, ?_⟩
  dsimp only
  rw [PSTRWordSegments.run_add, prepare_run rom whole start hc hwords hpcfit state hp ha]
  refine ⟨result.1, ?_, result.2.2.1.trans ready.2.2.2.2, result.2.2.2⟩
  exact result.2.1.trans (congrArg (BitVec.ofNat bits)
    (show 5 * (start + 51 + 36) = 5 * (start + 87) by omega))

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits)
    (steps : Nat) (hs : steps ≤ 87) :
    (packingDynamicTrace rom whole steps state).length ≤ 1044 := by
  have ht := packingDynamicTrace_length_le rom whole steps state
  omega

end PaperProofs.Structure.LaminarTree.PSTRNodeLeaf
