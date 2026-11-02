module

public import Structure.PSTR_HD_ZeroDeclHeap_134
public import Structure.PSTR_HD_HeadsZeroQuery_096

/-! Actual23op ORIGINAL q0 declaration segment in any literal containing
program. Reuses frozen011 values/heap and013 original nextConfiguration and
callback words. Only ORIGINAL Allowed correct/error declarations occur;
the old query segment is not reproved or strengthened. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

theorem declaration_segment {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (command : Command) (declaration : command = .correct ∨ command = .error)
    (allowed : Allowed full configuration command) (whole : List PackingOp) (start heapWords : Nat)
    (hbound : start + PSTRZeroLive.program.length ≤ whole.length)
    (hcode : ∀ i (hi : i < PSTRZeroLive.program.length), whole[start + i]'(by omega) = PSTRZeroLive.program[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hb : 8 ≤ bits) (hh : 6 ≤ heapWords) (hN1 : Fits bits (full.length + 1))
    (rep : HeapRepresents 0 full 0 configuration state.heap) :
    let after := packingRun (callInput 0 full command) whole 23 state
    after.pc = BitVec.ofNat bits (5 * (start + 23)) ∧ after.halted = false ∧
    after.heap = Function.update (Function.update state.heap (BitVec.ofNat bits 5)
      (BitVec.ofNat bits (PSTRZeroLive.failedWord command))) (BitVec.ofNat bits 4)
      (BitVec.ofNat bits (configuration.stage + PSTRZeroLive.increment command)) ∧
    HeapRepresents 0 full 0 (nextConfiguration 0 full configuration command) after.heap ∧
    (∀ cursor : configuration.stage < full.length + 1,
      ReplyCorrect 0 (callback 0 full ⟨configuration.stage, cursor⟩ configuration.used) (replyState 0 0 after)) ∧
    (∀ clock < 23, AtSafe (callInput 0 full command) whole heapWords (packingRun (callInput 0 full command) whole clock state)) ∧
    (∀ clock ≤ 23, ∀ physical, Fits bits physical → physical ≠ 4 → physical ≠ 5 →
      (packingRun (callInput 0 full command) whole clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical)) := by
  dsimp only
  let rom := callInput 0 full command
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have hslt := (declaration_allowed_fields full configuration command declaration allowed).2
  have hN : Fits bits full.length := (Nat.le_succ _).trans_lt hN1
  have hs : Fits bits configuration.stage := hslt.trans hN
  have hs1 : Fits bits (configuration.stage + 1) := (Nat.succ_le_of_lt hslt).trans_lt hN
  have values := PSTRZeroLive.execute_values full command configuration.stage state hb hN hs hs1
    (PSTRZeroLive.stage_word full configuration state.heap rep)
  have numbers := PSTRZeroLive.next_numbers full configuration command allowed
  have nextFit : Fits bits (nextConfiguration 0 full configuration command).stage := by
    rw [numbers.1]
    cases command <;> simp only [PSTRZeroLive.increment, Nat.add_zero] <;> assumption
  have run23 : packingRun rom whole 23 state = executeOps rom PSTRZeroLive.program state :=
    straight_segment rom whole PSTRZeroLive.program start hbound hcode PSTRZeroLive.program_straight hwords hpcfit state hp ha
  have pureRep : HeapRepresents 0 full 0 (nextConfiguration 0 full configuration command)
      (executeOps rom PSTRZeroLive.program state).heap := by
    rw [values.2.2.2.2]
    have updated := PSTRZeroLive.represents_update full configuration (nextConfiguration 0 full configuration command)
      state.heap hb nextFit rep
    simpa only [numbers.1, numbers.2] using updated
  have hR : Fits bits (PSTRZeroLive.rankWord full.length configuration.stage) := by
    unfold PSTRZeroLive.rankWord Fits
    split <;> omega
  have hG : Fits bits (PSTRZeroLive.goodWord full.length configuration.stage) := by
    unfold PSTRZeroLive.goodWord Fits
    split <;> omega
  have access : PrefixOK rom heapWords (fun _ => False) PSTRZeroLive.program state := by
    constructor
    · exact PSTRZeroLive.access_prefix full command heapWords state hb hh
    · intro clock hc physical hf impossible
      exact False.elim impossible
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run23, executeOps_pc rom PSTRZeroLive.program state PSTRZeroLive.program_straight, hp, BitVec.ofNat_add_ofNat]
    congr 1
  · rw [run23, executeOps_halted]
    exact ha
  · rw [run23]
    exact values.2.2.2.2
  · rw [run23]
    exact pureRep
  · intro cursor
    have cr := PSTRZeroLive.callback_words full ⟨configuration.stage, cursor⟩ configuration.used
    rw [run23]
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
    exact (straight_prefix_safe rom whole PSTRZeroLive.program heapWords start (fun _ => False) hbound hcode
      PSTRZeroLive.program_straight hwords hpcfit state hp ha access clock hc).1
  · intro clock hc physical hf h4 h5
    rw [fetched_prefix rom whole PSTRZeroLive.program start hbound hcode PSTRZeroLive.program_straight hwords hpcfit state hp ha clock hc]
    exact live_prefix_frame full command state hb physical hf h4 h5 clock hc

end PaperProofs.Structure.LaminarTree.PSTRZeroDeclaration
