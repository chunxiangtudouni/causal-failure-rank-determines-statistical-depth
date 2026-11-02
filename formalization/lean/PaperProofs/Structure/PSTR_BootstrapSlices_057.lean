module

public import PaperProofs.Structure.PSTR_CountBootstrapCode_039

/-! Literal bootstrap slices in an arbitrary ONE containing live program.
Its real width loop is never run as a halted helper and restarted. Code/
PC fit belong to the complete containing program and remain explicit here. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBootstrapSlices

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

theorem prefix_index_bound (whole : List PackingOp) (hbound : 61 ≤ whole.length)
    (i : Nat) (hi : i < PSTRCountBootstrapCode.program.length) : i < whole.length := by
  rw [PSTRCountBootstrapCode.program_length] at hi
  omega

structure Contains (whole : List PackingOp) : Prop where
  bound : 61 ≤ whole.length
  code : ∀ i (hi : i < PSTRCountBootstrapCode.program.length),
    whole[i]'(prefix_index_bound whole bound i hi) = PSTRCountBootstrapCode.program[i]

theorem width_contains (whole : List PackingOp) (hc : Contains whole) : PSTRWidthKernel.Contains whole 8 := by
  refine ⟨by have hb := hc.bound; rw [PSTRWidthKernel.kernel_length]; omega, ?_⟩
  intro i hi
  have hh := hc.code (8 + i) (by
    rw [PSTRCountBootstrapCode.program_length, PSTRWidthKernel.kernel_length] at *
    omega)
  exact hh.trans (PSTRCountBootstrapCode.contains_width.code i hi)

theorem header_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (hc : Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom whole 8 state = executeOps rom PSTRLiveHeader.program state := by
  apply PSTRWordSegments.straight_segment rom whole PSTRLiveHeader.program 0
    (by have hb := hc.bound; rw [PSTRLiveHeader.program_length]; omega) ?_
    PSTRLiveHeader.program_straight hw hpcfit state hp ha
  intro i hi
  have hh := hc.code i (by rw [PSTRCountBootstrapCode.program_length]; rw [PSTRLiveHeader.program_length] at hi; omega)
  have he : PSTRCountBootstrapCode.program[i]'(by rw [PSTRCountBootstrapCode.program_length]; rw [PSTRLiveHeader.program_length] at hi; omega) =
      PSTRLiveHeader.program[i] := by
    change i < 8 at hi
    interval_cases i <;> rfl
  simpa only [Nat.zero_add] using hh.trans he

theorem width_run {bits q : Nat} (whole : List PackingOp) (hc : Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (full : List (Finset (Fin q))) (command : Command) (heap : BitVec bits → BitVec bits)
    (hb : 8 ≤ bits) (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hroom : Fits bits (2 * (q + 1))) :
    let after := packingRun (callInput q full command) whole (8 * CapacityBits.width q + 16) (packingInitial heap)
    after.halted = false ∧ after.pc = BitVec.ofNat bits 105 ∧
      after.register .total = BitVec.ofNat bits (CapacityBits.width q) ∧
      after.register .flag = AlgorithmClaims.PackedCapacityRAM.lowMask bits (CapacityBits.width q) ∧ after.heap = heap := by
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
  have hm : 8 + 12 < whole.length := by have hh := hc.bound; omega
  have mask : whole[8 + 12]'hm = PSTRWidthEmbedded.maskOp :=
    (hc.code 20 (by rw [PSTRCountBootstrapCode.program_length]; decide)).trans (by rfl)
  have result := PSTRWidthEmbedded.actual_width_mask rom whole 8 (width_contains whole hc) hw hpcfit
    (by have hh := hc.bound; omega) mask q current hf hp ha hroom
  dsimp only
  rw [show 8 * CapacityBits.width q + 16 = 8 + (8 * CapacityBits.width q + 8) by omega,
    PSTRWordSegments.run_add, header_run rom whole hc hw hpcfit (packingInitial heap) rfl rfl]
  exact ⟨result.1, result.2.1, result.2.2.1.counter, result.2.2.2.1,
    result.2.2.2.2.trans (PSTRLiveHeader.execute_heap rom (packingInitial heap))⟩

theorem park_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (hc : Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits 105) (ha : state.halted = false) :
    packingRun rom whole 3 state = executeOps rom PSTRCountInit.park state := by
  apply PSTRCountInit.containing_park rom whole 21
    (by have h := hc.bound; rw [PSTRCountInit.park_length]; omega) ?_ hw hpcfit state hp ha
  intro i hi
  have hh := hc.code (21 + i) (by rw [PSTRCountBootstrapCode.program_length]; rw [PSTRCountInit.park_length] at hi; omega)
  have he : PSTRCountBootstrapCode.program[21 + i]'(by rw [PSTRCountBootstrapCode.program_length]; rw [PSTRCountInit.park_length] at hi; omega) =
      PSTRCountInit.park[i] := by
    change i < 3 at hi
    interval_cases i <;> rfl
  exact hh.trans he

theorem workspace_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (hc : Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits 120) (ha : state.halted = false) :
    packingRun rom whole 19 state = executeOps rom PSTRCountWorkspace.program state := by
  apply PSTRCountWorkspace.containing_base rom whole 24
    (by have h := hc.bound; rw [PSTRCountWorkspace.program_length]; omega) ?_ hw hpcfit state hp ha
  intro i hi
  have hh := hc.code (24 + i) (by rw [PSTRCountBootstrapCode.program_length]; rw [PSTRCountWorkspace.program_length] at hi; omega)
  have he : PSTRCountBootstrapCode.program[24 + i]'(by rw [PSTRCountBootstrapCode.program_length]; rw [PSTRCountWorkspace.program_length] at hi; omega) =
      PSTRCountWorkspace.program[i] := by
    change i < 19 at hi
    interval_cases i <;> rfl
  exact hh.trans he

theorem init_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (hc : Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits 215) (ha : state.halted = false) :
    packingRun rom whole 18 state = executeOps rom PSTRCountInit.program state := by
  apply PSTRCountInit.containing_init rom whole 43
    (by have h := hc.bound; rw [PSTRCountInit.program_length]; omega) ?_ hw hpcfit state hp ha
  intro i hi
  have hh := hc.code (43 + i) (by rw [PSTRCountBootstrapCode.program_length]; rw [PSTRCountInit.program_length] at hi; omega)
  have he : PSTRCountBootstrapCode.program[43 + i]'(by rw [PSTRCountBootstrapCode.program_length]; rw [PSTRCountInit.program_length] at hi; omega) =
      PSTRCountInit.program[i] := by
    change i < 18 at hi
    interval_cases i <;> rfl
  exact hh.trans he

end PaperProofs.Structure.LaminarTree.PSTRBootstrapSlices
