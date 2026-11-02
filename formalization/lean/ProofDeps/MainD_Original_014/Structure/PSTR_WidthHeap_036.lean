module

public import Structure.PSTR_WidthPrologue_034
public import Structure.PSTR_WidthPrefix_035
public import Structure.PSTR_LiveHeaderSafety_004

/-! The fixed raw-input prologue preserves every physical heap word at every
clock, including its actual terminal HALT. All packed capacity-prefix bounds
therefore persist without an initialized-scratch or decoded-input premise. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRWidthHeap

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PSTRWidthPrologue

theorem header_prefix {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 8 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ 8) :
    packingRun rom program clock state = executeOps rom (PSTRLiveHeader.program.take clock) state := by
  apply PSTRWidthPrefix.straight_prefix rom program PSTRLiveHeader.program 0 (by decide) ?_
    PSTRLiveHeader.program_straight (code_fit hb) (pc_fit hb) state hp ha clock hc
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

theorem active_prefix_heap {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hroom : Fits bits (2 * (q + 1))) (clock : Nat)
    (hc : clock ≤ 8 * CapacityBits.width q + 16) :
    (packingRun (callInput q full command) program clock (packingInitial heap)).heap = heap := by
  let rom := callInput q full command
  by_cases hfirst : clock ≤ 8
  · rw [header_prefix rom (packingInitial heap) hb rfl rfl clock hfirst]
    exact PSTRLiveHeader.execute_prefix_heap rom (packingInitial heap) clock
  · let current := executeOps rom PSTRLiveHeader.program (packingInitial heap)
    have hq : Fits bits q := by unfold Fits at hroom ⊢; omega
    have regs := PSTRLiveHeader.execute_registers full command (packingInitial heap) hb hN hq hpos
    have hf : (current.register .fresh).toNat = q := by
      rw [regs.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
    have hp : current.pc = BitVec.ofNat bits (5 * 8) := by
      rw [executeOps_pc rom PSTRLiveHeader.program (packingInitial heap) PSTRLiveHeader.program_straight]
      change BitVec.ofNat bits 0 + BitVec.ofNat bits (5 * PSTRLiveHeader.program.length) = _
      rw [BitVec.zero_add, PSTRLiveHeader.program_length]
    have ha : current.halted = false := by rw [executeOps_halted]; rfl
    rw [show clock = 8 + (clock - 8) by omega, PSTRWordSegments.run_add,
      header_run rom (packingInitial heap) hb rfl rfl]
    exact (PSTRWidthPrefix.width_mask_prefix_heap rom program 8 contains_width (code_fit hb) (pc_fit hb)
      (by decide) (by rfl) q current hf hp ha hroom (clock - 8) (by omega)).trans
      (PSTRLiveHeader.execute_heap rom (packingInitial heap))

theorem halt_run {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hroom : Fits bits (2 * (q + 1))) :
    packingRun (callInput q full command) program (8 * CapacityBits.width q + 17) (packingInitial heap) =
      { packingRun (callInput q full command) program (8 * CapacityBits.width q + 16) (packingInitial heap)
        with halted := true } := by
  have result := actual_width_mask full command heap hb hN hpos hroom
  have hpc : (packingRun (callInput q full command) program (8 * CapacityBits.width q + 16)
      (packingInitial heap)).pc.toNat = 5 * program.length := by
    rw [result.2.1, program_length, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (pc_fit hb)
  rw [show 8 * CapacityBits.width q + 17 = (8 * CapacityBits.width q + 16) + 1 by omega,
    packingRun_succ, packingStep_halt _ _ _ (code_fit hb) hpc result.1]

theorem all_prefix_heap {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hroom : Fits bits (2 * (q + 1))) (clock : Nat)
    (hc : clock ≤ 8 * CapacityBits.width q + 17) :
    (packingRun (callInput q full command) program clock (packingInitial heap)).heap = heap := by
  by_cases hbefore : clock ≤ 8 * CapacityBits.width q + 16
  · exact active_prefix_heap full command heap hb hN hpos hroom clock hbefore
  · have he : clock = 8 * CapacityBits.width q + 17 := by omega
    subst clock
    rw [halt_run full command heap hb hN hpos hroom]
    exact active_prefix_heap full command heap hb hN hpos hroom _ le_rfl

theorem all_prefix_capacity {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hroom : Fits bits (2 * (q + 1)))
    (bounded : CapacityPrefixBounded q capWords (logicalHeap q capWords heap))
    (clock : Nat) (hc : clock ≤ 8 * CapacityBits.width q + 17) :
    CapacityPrefixBounded q capWords (logicalHeap q capWords
      (packingRun (callInput q full command) program clock (packingInitial heap)).heap) := by
  rw [all_prefix_heap full command heap hb hN hpos hroom clock hc]
  exact bounded

theorem halted {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hroom : Fits bits (2 * (q + 1))) :
    (packingRun (callInput q full command) program (8 * CapacityBits.width q + 17) (packingInitial heap)).halted = true := by
  rw [halt_run full command heap hb hN hpos hroom]

end PaperProofs.Structure.LaminarTree.PSTRWidthHeap
