module

public import Structure.PSTR_HD_CountSetupSafe_042

/-! Transfer proved straight-block access/frame prefixes to the actual
fetched Word execution in the single containing program. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open RawTreePreprocessingClaims

theorem fetched_prefix {bits : Nat} (rom : PhysicalROM) (containing block : List PackingOp) (start : Nat)
    (hbound : start + block.length ≤ containing.length)
    (hcode : ∀ i (hi : i < block.length), containing[start + i]'(by omega) = block[i])
    (hs : StraightProgram block) (hw : WordsFit bits (packingCode containing))
    (hpcfit : Fits bits (5 * containing.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ block.length) :
    packingRun rom containing count state = executeOps rom (block.take count) state := by
  have hl : (block.take count).length = count := List.length_take_of_le hc
  conv_lhs => rw [← hl]
  apply straight_segment rom containing (block.take count) start (by omega) ?_ ?_ hw hpcfit state hp ha
  · intro i hi
    have hi' : i < block.length := by rw [hl] at hi; omega
    simpa only [List.getElem_take] using hcode i hi'
  · intro op ho
    exact hs op (List.mem_of_mem_take ho)

theorem fetched_prefix_pc {bits : Nat} (rom : PhysicalROM) (containing block : List PackingOp) (start : Nat)
    (hbound : start + block.length ≤ containing.length)
    (hcode : ∀ i (hi : i < block.length), containing[start + i]'(by omega) = block[i])
    (hs : StraightProgram block) (hw : WordsFit bits (packingCode containing))
    (hpcfit : Fits bits (5 * containing.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ block.length) :
    (packingRun rom containing count state).pc.toNat = 5 * (start + count) := by
  rw [fetched_prefix rom containing block start hbound hcode hs hw hpcfit state hp ha count hc,
    executeOps_pc rom _ state (fun op ho => hs op (List.mem_of_mem_take ho)), hp,
    List.length_take_of_le hc, BitVec.ofNat_add_ofNat]
  have he : 5 * start + 5 * count = 5 * (start + count) := by omega
  rw [he, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 (by omega : start + count ≤ containing.length)).trans_lt hpcfit)

theorem fetched_prefix_safe {bits : Nat} (rom : PhysicalROM) (containing block : List PackingOp)
    (heapWords start : Nat) (region : Nat → Prop)
    (hbound : start + block.length ≤ containing.length)
    (hcode : ∀ i (hi : i < block.length), containing[start + i]'(by omega) = block[i])
    (hs : StraightProgram block) (hw : WordsFit bits (packingCode containing))
    (hpcfit : Fits bits (5 * containing.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (safe : PrefixOK rom heapWords region block state) (count : Nat) (hc : count < block.length) :
    let result := packingRun rom containing count state
    result.halted = false ∧ result.pc.toNat + 4 < (packingCode containing).length ∧
    PackingOp.decode (fetch containing result) = some block[count] ∧
    packingAccessFits rom heapWords result block[count] ∧ HeapFrame region state.heap result.heap := by
  have he := fetched_prefix rom containing block start hbound hcode hs hw hpcfit state hp ha count hc.le
  have hpc := fetched_prefix_pc rom containing block start hbound hcode hs hw hpcfit state hp ha count hc.le
  have hindex : start + count < containing.length := by omega
  have hf : fetch containing (packingRun rom containing count state) = natFetch containing (5 * (start + count)) := by
    change physicalFetch bits (packingCode containing) _ = _
    rw [physicalFetch_eq bits _ _ hw, hpc]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he, executeOps_halted, ha]
  · rw [hpc, packingCode_length]
    omega
  · rw [hf, natFetch_body containing (start + count) hindex, hcode count hc, decode_encode]
  · rw [he]
    exact safe.access count hc
  · rw [he]
    exact safe.frame count hc.le

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
