module

public import PaperProofs.Structure.PSTR_WidthPrologue_034
public import PaperProofs.Structure.PSTR_CountInit_038
public import PaperProofs.Structure.PSTR_HD_CountWorkspace_025

/-! One fixed containing program, selected before all raw inputs. Runtime
width/mask computation, register parking, the actual metadata-end locator,
and real four-slot initialization are consecutive actual code segments. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountBootstrapCode

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

def program : List PackingOp :=
  PSTRWidthPrologue.program ++ PSTRCountInit.park ++ PSTRCountWorkspace.program ++ PSTRCountInit.program

theorem program_length : program.length = 61 := rfl
theorem code_length : (packingCode program).length = 310 := by rw [packingCode_length, program_length]

set_option maxRecDepth 10000 in
theorem code_fit {bits : Nat} (hb : 9 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 512 ≤ 2 ^ bits :=
    (show 2 ^ 9 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  simp [packingCode, program, PSTRWidthPrologue.program, PSTRLiveHeader.program,
    PSTRWidthKernel.kernel, PSTRRuntimeWidth.initCode, PSTRWidthKernel.testAt,
    PSTRWidthKernel.testLeadAt, PSTRWidthKernel.bodyAt, PSTRWidthKernel.bodyLeadAt,
    PSTRWidthEmbedded.maskOp, PSTRCountInit.park, PSTRCountInit.program,
    PSTRCountInit.head, PSTRCountInit.tail, PSTRReplySpill.spillProgram,
    PSTRCountWorkspace.program, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
  unfold Fits
  omega

theorem pc_fit {bits : Nat} (hb : 9 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 512 ≤ 2 ^ bits :=
    (show 2 ^ 9 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 305 < 2 ^ bits
  omega

theorem contains_width : PSTRWidthKernel.Contains program 8 := by
  refine ⟨by decide, ?_⟩
  intro i hi
  change i < 12 at hi
  interval_cases i <;> rfl

theorem header_run {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 9 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom program 8 state = executeOps rom PSTRLiveHeader.program state := by
  apply PSTRWordSegments.straight_segment rom program PSTRLiveHeader.program 0 (by decide) ?_
    PSTRLiveHeader.program_straight (code_fit hb) (pc_fit hb) state hp ha
  intro i hi
  change i < 8 at hi
  interval_cases i <;> rfl

theorem width_run {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) (hb : 9 ≤ bits)
    (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hroom : Fits bits (2 * (q + 1))) :
    let after := packingRun (callInput q full command) program (8 * CapacityBits.width q + 16) (packingInitial heap)
    after.halted = false ∧ after.pc = BitVec.ofNat bits 105 ∧
      after.register .total = BitVec.ofNat bits (CapacityBits.width q) ∧
      after.register .flag = AlgorithmClaims.PackedCapacityRAM.lowMask bits (CapacityBits.width q) ∧
      after.heap = heap := by
  let rom := callInput q full command
  let current := executeOps rom PSTRLiveHeader.program (packingInitial heap)
  have hb8 : 8 ≤ bits := by omega
  have hq : Fits bits q := by unfold Fits at hroom ⊢; omega
  have regs := PSTRLiveHeader.execute_registers full command (packingInitial heap) hb8 hN hq hpos
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

theorem park_run {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 9 ≤ bits) (hp : state.pc = BitVec.ofNat bits 105) (ha : state.halted = false) :
    packingRun rom program 3 state = executeOps rom PSTRCountInit.park state := by
  apply PSTRCountInit.containing_park rom program 21 (by decide) ?_ (code_fit hb) (pc_fit hb) state hp ha
  intro i hi
  change i < 3 at hi
  interval_cases i <;> rfl

theorem workspace_run {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 9 ≤ bits) (hp : state.pc = BitVec.ofNat bits 120) (ha : state.halted = false) :
    packingRun rom program 19 state = executeOps rom PSTRCountWorkspace.program state := by
  apply PSTRCountWorkspace.containing_base rom program 24 (by decide) ?_ (code_fit hb) (pc_fit hb) state hp ha
  intro i hi
  change i < 19 at hi
  interval_cases i <;> rfl

theorem init_run {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 9 ≤ bits) (hp : state.pc = BitVec.ofNat bits 215) (ha : state.halted = false) :
    packingRun rom program 18 state = executeOps rom PSTRCountInit.program state := by
  apply PSTRCountInit.containing_init rom program 43 (by decide) ?_ (code_fit hb) (pc_fit hb) state hp ha
  intro i hi
  change i < 18 at hi
  interval_cases i <;> rfl

theorem trace_bound {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) :
    (packingDynamicTrace (callInput q full command) program (8 * CapacityBits.width q + 56) (packingInitial heap)).length ≤
      96 * CapacityBits.width q + 672 := by
  have ht := packingDynamicTrace_length_le (callInput q full command) program
    (8 * CapacityBits.width q + 56) (packingInitial heap)
  omega

theorem call_cost {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) :
    callCost q full program command (8 * CapacityBits.width q + 56) heap ≤
      96 * CapacityBits.width q + 991 := by
  have ht := trace_bound full command heap
  unfold callCost
  rw [code_length]
  omega

end PaperProofs.Structure.LaminarTree.PSTRCountBootstrapCode
