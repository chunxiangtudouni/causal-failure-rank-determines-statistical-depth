module

public import PaperProofs.Structure.PSTR_UniformBootstrapCode_105

/-! Actual raw-input header/width/guard entry for BOTH q branches, with
arbitrary seven incoming registers. All18+8width steps are real fetched
instructions of the same containing code. No packingInitial restart. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRUniformWidthEntry

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRUniformBootstrapCode

theorem width_run {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (hb : 8 ≤ bits) (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hroom : Fits bits (2 * (q + 1))) :
    let after := packingRun (callInput q full command) whole (8 * CapacityBits.width q + 16) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits 105 ∧
      after.register .total = BitVec.ofNat bits (CapacityBits.width q) ∧
      after.register .flag = lowMask bits (CapacityBits.width q) ∧ after.heap = state.heap := by
  let rom := callInput q full command
  let current := executeOps rom PSTRLiveHeader.program state
  have hq : Fits bits q := by unfold Fits at hroom ⊢; omega
  have regs := PSTRLiveHeader.execute_registers full command state hb hN hq hpos
  have hf : (current.register .fresh).toNat = q := by
    rw [regs.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  have pc : current.pc = BitVec.ofNat bits (5 * 8) := by
    rw [executeOps_pc rom PSTRLiveHeader.program state PSTRLiveHeader.program_straight,
      hp, PSTRLiveHeader.program_length, BitVec.zero_add]
  have active : current.halted = false := by rw [executeOps_halted, ha]
  have result := PSTRWidthEmbedded.actual_width_mask rom whole 8 (width_contains whole zeroTarget cb)
    hwords hpcfit (by have h := cb.bound; rw [program_length] at h; omega)
    (mask_code whole zeroTarget cb) q current hf pc active hroom
  dsimp only
  rw [show 8 * CapacityBits.width q + 16 = 8 + (8 * CapacityBits.width q + 8) by omega,
    PSTRWordSegments.run_add, header_run rom whole zeroTarget cb hwords hpcfit state hp ha]
  exact ⟨result.1, result.2.1, result.2.2.1.counter, result.2.2.2.1,
    result.2.2.2.2.trans (PSTRLiveHeader.execute_heap rom state)⟩

theorem actual_entry {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false) :
    let after := packingRun (callInput q full command) whole (8 * CapacityBits.width q + 18) state
    after.halted = false ∧
      after.pc = (if q = 0 then BitVec.ofNat (indexWidth 32 full.length q) (5 * zeroTarget)
        else BitVec.ofNat (indexWidth 32 full.length q) 115) ∧
      after.register .total = BitVec.ofNat (indexWidth 32 full.length q) (CapacityBits.width q) ∧
      after.register .flag = lowMask (indexWidth 32 full.length q) (CapacityBits.width q) ∧
      after.heap = state.heap := by
  let rom := callInput q full command
  let wide := packingRun rom whole (8 * CapacityBits.width q + 16) state
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have rooms := PSTROriginalCountRoom.raw_rooms full.length q
  have width := width_run full command whole zeroTarget cb hwords hpcfit state hp ha
    (by omega) rooms.1 rooms.2.1 rooms.2.2
  have result := PSTRZeroWidthGuard.actual_result full rom whole 21 zeroTarget
    (guard_contains whole zeroTarget cb) hwords hpcfit wide width.2.1 width.1 width.2.2.1
  dsimp only
  rw [show 8 * CapacityBits.width q + 18 = (8 * CapacityBits.width q + 16) + 2 by omega,
    PSTRWordSegments.run_add]
  exact ⟨result.1, result.2.1,
    (result.2.2.2 .total (by decide)).trans width.2.2.1,
    (result.2.2.2 .flag (by decide)).trans width.2.2.2.1,
    result.2.2.1.trans width.2.2.2.2⟩

end PaperProofs.Structure.LaminarTree.PSTRUniformWidthEntry
