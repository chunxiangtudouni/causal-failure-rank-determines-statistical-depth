module

public import PaperProofs.Structure.PSTR_WidthEmbedded_033
public import PaperProofs.Structure.PSTR_LiveHeader_003

/-! A single fixed positive-query prologue starts from packingInitial and
the ORIGINAL callInput, loads q, computes width and mask, and exits ACTIVE.
No internal register answer or helper-HALT restart is a caller premise. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRWidthPrologue

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def program : List PackingOp :=
  PSTRLiveHeader.program ++ PSTRWidthKernel.kernel 8 ++ [PSTRWidthEmbedded.maskOp]

theorem program_length : program.length = 21 := rfl
theorem code_length : (packingCode program).length = 110 := by rw [packingCode_length, program_length]

set_option maxRecDepth 10000 in
theorem code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  simp [packingCode, program, PSTRLiveHeader.program, PSTRWidthKernel.kernel,
    PSTRRuntimeWidth.initCode, PSTRWidthKernel.testAt, PSTRWidthKernel.testLeadAt,
    PSTRWidthKernel.bodyAt, PSTRWidthKernel.bodyLeadAt, PSTRWidthEmbedded.maskOp,
    PackingOp.encode, Op.encodeWords, Instruction.encodeWords, PackingPrimitive.word,
    Register.word, Region.word, haltWords] at hv
  unfold Fits
  omega

theorem pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 105 < 2 ^ bits
  omega

theorem contains_width : PSTRWidthKernel.Contains program 8 := by
  refine ⟨by decide, ?_⟩
  intro i hi
  change ((PSTRLiveHeader.program ++ PSTRWidthKernel.kernel 8) ++ [PSTRWidthEmbedded.maskOp])[8 + i]'(by
    change 8 + i < 21
    have hh : i < 12 := hi
    omega) = _
  rw [List.getElem_append_left (by change 8 + i < 20; have hh : i < 12 := hi; omega),
    List.getElem_append_right (by change 8 ≤ 8 + i; omega)]
  simp only [PSTRLiveHeader.program_length, Nat.add_sub_cancel_left]

theorem header_run {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 8 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom program 8 state = executeOps rom PSTRLiveHeader.program state := by
  apply PSTRWordSegments.straight_segment rom program PSTRLiveHeader.program 0 (by decide) ?_
    PSTRLiveHeader.program_straight (code_fit hb) (pc_fit hb) state hp ha
  intro i hi
  have hmid : i < (PSTRLiveHeader.program ++ PSTRWidthKernel.kernel 8).length := by
    change i < 20
    have hh : i < 8 := hi
    omega
  simpa only [Nat.zero_add] using (show program[i]'(by
    rw [program_length]
    have hh : i < 8 := hi
    omega) = PSTRLiveHeader.program[i] from by
      change ((PSTRLiveHeader.program ++ PSTRWidthKernel.kernel 8) ++ [PSTRWidthEmbedded.maskOp])[i]'(by
        change i < 21
        have hh : i < 8 := hi
        omega) = _
      rw [List.getElem_append_left hmid, List.getElem_append_left hi])

theorem actual_width_mask {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hroom : Fits bits (2 * (q + 1))) :
    let after := packingRun (callInput q full command) program (8 * CapacityBits.width q + 16) (packingInitial heap)
    after.halted = false ∧ after.pc = BitVec.ofNat bits 105 ∧
      after.register .total = BitVec.ofNat bits (CapacityBits.width q) ∧
      after.register .flag = lowMask bits (CapacityBits.width q) ∧ after.heap = heap := by
  let rom := callInput q full command
  let current := executeOps rom PSTRLiveHeader.program (packingInitial heap)
  have hq : Fits bits q := by unfold Fits at hroom ⊢; omega
  have regs := PSTRLiveHeader.execute_registers full command (packingInitial heap) hb hN hq hpos
  have hf : (current.register .fresh).toNat = q := by
    rw [regs.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  have hp : current.pc = BitVec.ofNat bits (5 * 8) := by
    rw [executeOps_pc rom PSTRLiveHeader.program (packingInitial heap) PSTRLiveHeader.program_straight]
    change BitVec.ofNat bits 0 + BitVec.ofNat bits (5 * PSTRLiveHeader.program.length) = _
    rw [BitVec.zero_add, PSTRLiveHeader.program_length]
  have ha : current.halted = false := by rw [executeOps_halted]; rfl
  have result := PSTRWidthEmbedded.actual_width_mask rom program 8 contains_width (code_fit hb) (pc_fit hb)
    (by decide) (by rfl) q current hf hp ha hroom
  dsimp only
  rw [show 8 * CapacityBits.width q + 16 = 8 + (8 * CapacityBits.width q + 8) by omega,
    PSTRWordSegments.run_add, header_run rom (packingInitial heap) hb rfl rfl]
  exact ⟨result.1, result.2.1, result.2.2.1.counter, result.2.2.2.1,
    result.2.2.2.2.trans (PSTRLiveHeader.execute_heap rom (packingInitial heap))⟩

theorem trace_bound {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) :
    (packingDynamicTrace (callInput q full command) program (8 * CapacityBits.width q + 16) (packingInitial heap)).length ≤
      96 * CapacityBits.width q + 192 := by
  have ht := packingDynamicTrace_length_le (callInput q full command) program
    (8 * CapacityBits.width q + 16) (packingInitial heap)
  omega

theorem call_cost {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) :
    callCost q full program command (8 * CapacityBits.width q + 16) heap ≤
      96 * CapacityBits.width q + 311 := by
  have ht := trace_bound full command heap
  unfold callCost
  rw [code_length]
  omega

end PaperProofs.Structure.LaminarTree.PSTRWidthPrologue
