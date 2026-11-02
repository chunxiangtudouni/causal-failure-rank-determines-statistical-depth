module

public import PaperProofs.Structure.PSTR_HD_HeadsZeroOriginalIteration_095
public import PaperProofs.Structure.PSTR_HD_ZeroLiveClaims_013

/-! The EXISTING frozen23op zero-tool live code is STRAIGHT and can be
fetched inline at any real code offset. On QUERY ROM and original failedfalse
heap it preserves the ENTIRE heap at every prefix. No implementation is
redesigned here; no reset, external call, query oracle or tree input is used. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

theorem zero_query_prefix_heap {bits : Nat} (full : List (Finset (Fin 0))) (stage : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hstage : state.heap (BitVec.ofNat bits 4) = BitVec.ofNat bits stage)
    (hfailed : state.heap (BitVec.ofNat bits 5) = BitVec.ofNat bits 0)
    (count : Nat) (hc : count ≤ PSTRZeroLive.program.length) :
    (executeOps (callInput 0 full .query) (PSTRZeroLive.program.take count) state).heap = state.heap := by
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have h2 : (BitVec.ofNat bits 2).toNat = 2 := Nat.mod_eq_of_lt (by omega)
  have store5 : Function.update state.heap (BitVec.ofNat bits 5) (BitVec.ofNat bits 0) = state.heap :=
    Function.update_eq_self_iff.mpr hfailed.symm
  have store4 : Function.update state.heap (BitVec.ofNat bits 4) (BitVec.ofNat bits stage) = state.heap :=
    Function.update_eq_self_iff.mpr hstage.symm
  rw [PSTRZeroLive.command_rom]
  change count ≤ 23 at hc
  interval_cases count <;>
    simp +decide [PSTRZeroLive.program, executeOps, packingExecuteOp, wordOp, wordInstruction,
      PhysicalROM.words, Command.word, h2, hstage, store5, store4, BitVec.ofNat_add_ofNat]

theorem zero_query_prefix_heap_rep {bits : Nat} (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (stage : Nat) (state : WordState bits) (hb : 8 ≤ bits)
    (rep : HeapRepresents 0 full 0 ⟨stage, used, false⟩ state.heap)
    (count : Nat) (hc : count ≤ PSTRZeroLive.program.length) :
    (executeOps (callInput 0 full .query) (PSTRZeroLive.program.take count) state).heap = state.heap := by
  have hnat : (state.heap (BitVec.ofNat bits 5)).toNat = 0 := by
    simpa [bit] using (zero_physical_stage_failed full ⟨stage, used, false⟩ state.heap hb rep).2
  have hword := congrArg (BitVec.ofNat bits) hnat
  have hfailed : state.heap (BitVec.ofNat bits 5) = BitVec.ofNat bits 0 := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hword
  exact zero_query_prefix_heap full stage state hb (zero_stage_word full ⟨stage, used, false⟩ state.heap hb rep) hfailed count hc

theorem zero_query_segment {bits : Nat} (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (stage : Fin (full.length + 1)) (whole : List PackingOp) (start heapWords : Nat)
    (hbound : start + PSTRZeroLive.program.length ≤ whole.length)
    (hcode : ∀ i (hi : i < PSTRZeroLive.program.length), whole[start + i]'(by omega) = PSTRZeroLive.program[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hb : 8 ≤ bits) (hh : 6 ≤ heapWords) (hN1 : Fits bits (full.length + 1))
    (rep : HeapRepresents 0 full 0 ⟨stage.val, used, false⟩ state.heap) :
    let after := packingRun (callInput 0 full .query) whole 23 state
    after.pc = BitVec.ofNat bits (5 * (start + 23)) ∧ after.halted = false ∧ after.heap = state.heap ∧
    ReplyCorrect 0 (callback 0 full stage used) (replyState 0 0 after) ∧
    (∀ clock ≤ 23, (packingRun (callInput 0 full .query) whole clock state).heap = state.heap) ∧
    (∀ clock < 23, AtSafe (callInput 0 full .query) whole heapWords (packingRun (callInput 0 full .query) whole clock state)) := by
  dsimp only
  let rom := callInput 0 full .query
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have hN : Fits bits full.length := (Nat.le_succ _).trans_lt hN1
  have hs : Fits bits stage.val := stage.isLt.trans hN1
  have hs1 : Fits bits (stage.val + 1) := (Nat.succ_le_of_lt stage.isLt).trans_lt hN1
  have values := PSTRZeroLive.execute_values full .query stage.val state hb hN hs hs1
    (zero_stage_word full ⟨stage.val, used, false⟩ state.heap hb rep)
  have cr := PSTRZeroLive.callback_words full stage used
  have hR : Fits bits (PSTRZeroLive.rankWord full.length stage.val) := by unfold PSTRZeroLive.rankWord Fits; split <;> omega
  have hG : Fits bits (PSTRZeroLive.goodWord full.length stage.val) := by unfold PSTRZeroLive.goodWord Fits; split <;> omega
  have run23 : packingRun rom whole 23 state = executeOps rom PSTRZeroLive.program state :=
    straight_segment rom whole PSTRZeroLive.program start hbound hcode PSTRZeroLive.program_straight hwords hpcfit state hp ha
  have prefixHeap (clock : Nat) (hc : clock ≤ 23) : (packingRun rom whole clock state).heap = state.heap := by
    rw [fetched_prefix rom whole PSTRZeroLive.program start hbound hcode PSTRZeroLive.program_straight hwords hpcfit state hp ha clock hc]
    exact zero_query_prefix_heap_rep full used stage.val state hb rep clock hc
  have safe : PrefixOK rom heapWords (fun _ => True) PSTRZeroLive.program state := by
    constructor
    · exact PSTRZeroLive.access_prefix full .query heapWords state hb hh
    · intro clock hc
      rw [zero_query_prefix_heap_rep full used stage.val state hb rep clock hc]
      exact heapFrame_refl _ _
  refine ⟨?_, ?_, prefixHeap 23 le_rfl, ?_, prefixHeap, ?_⟩
  · rw [run23, executeOps_pc rom PSTRZeroLive.program state PSTRZeroLive.program_straight, hp, BitVec.ofNat_add_ofNat]
    congr 1
  · rw [run23, executeOps_halted]
    exact ha
  · rw [run23]
    refine ⟨?_, ?_, ?_, ?_⟩
    · change ((executeOps rom PSTRZeroLive.program state).register .value).toNat = _
      rw [values.1, cr.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR]
    · change ((executeOps rom PSTRZeroLive.program state).register .old).toNat = _
      rw [values.2.1, cr.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hG]
    · change ((executeOps rom PSTRZeroLive.program state).register .fresh).toNat = _
      rw [values.2.2.1, cr.2.2.1]
      simp
    · change ((executeOps rom PSTRZeroLive.program state).register .index).toNat = _
      rw [values.2.2.2.1, cr.2.2.2]
      simp
  · intro clock hc
    exact (straight_prefix_safe rom whole PSTRZeroLive.program heapWords start (fun _ => True) hbound hcode
      PSTRZeroLive.program_straight hwords hpcfit state hp ha safe clock hc).1

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
