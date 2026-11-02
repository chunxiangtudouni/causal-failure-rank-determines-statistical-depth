module

public import Structure.PSTR_RuntimeWidthWord_006

/-! Complete physical Word execution of the fixed width loop. Its runtime
argument q is the ordinary fresh register, not a logarithm/rank/trace oracle.
Embedding and register loading into the original fixed live program remain
separate obligations; this theorem does not claim a complete A19 call. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRuntimeWidthRun

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open RawIncidenceLaminarRAM (runOps)
open PSTRRuntimeWidth PSTRRuntimeWidthWord

theorem finish_prefix {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : NatState)
    (hb : 8 ≤ bits) (hs : Ready q (CapacityBits.width q) state)
    (hr : RegistersFit bits state) (hq : Fits bits (q + 1))
    (count : Nat) (hc : count ≤ 4) : Point bits (natRun rom program count state) := by
  by_cases ht : count ≤ 3
  · exact test_prefix rom q (CapacityBits.width q) state hb hs hr hq count ht
  · have he : count = 4 := by omega
    subst count
    have htest := test_prefix rom q (CapacityBits.width q) state hb hs hr hq 3 le_rfl
    let tested := runOps rom testCode state
    have hle : q + 1 ≤ 2 ^ CapacityBits.width q := Nat.le_pow_clog (by decide) (q + 1)
    have hz : q + 1 - 2 ^ CapacityBits.width q = 0 := Nat.sub_eq_zero_of_le hle
    have hp : tested.pc = 5 * program.length := by
      simp +decide [tested, testCode, testLead, runOps, natExecuteOp, Op.execute,
        Instruction.execute, hs.old, hs.power, hz, program_length]
    have ha : tested.halted = false := by
      simp only [tested, RawIncidenceLaminarRAM.runOps_halted, hs.active]
    have hhalt : natRun rom program 1 tested = { tested with halted := true } :=
      natStep_halt rom program tested hp ha
    rw [show 4 = 3 + 1 from rfl, natRun_add, test_run rom state hs.pc hs.active, hhalt]
    rw [test_run rom state hs.pc hs.active] at htest
    exact htest

theorem all_prefixes {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : NatState)
    (hb : 8 ≤ bits) (hf : state.register .fresh = q)
    (hp : state.pc = 0) (ha : state.halted = false) (hr : RegistersFit bits state)
    (hq : Fits bits (q + 1)) (hpower : Fits bits (2 ^ CapacityBits.width q)) :
    ∀ clock ≤ 8 * CapacityBits.width q + 8, Point bits (natRun rom program clock state) := by
  intro clock hc
  by_cases hfirst : clock ≤ 4
  · exact init_prefix rom q state hb hf hp ha hr hq clock hfirst
  · have he : clock = 4 + (clock - 4) := by omega
    rw [he, natRun_add]
    let built := natRun rom program 4 state
    have hinit := (init_ready rom q state hf hp ha).1
    have hreg := (init_prefix rom q state hb hf hp ha hr hq 4 le_rfl).1
    by_cases hloop : clock - 4 ≤ 8 * CapacityBits.width q
    · exact loop_all_prefixes rom q 0 (CapacityBits.width q) built hb hinit hreg hq hpower
        (by omega) (clock - 4) hloop
    · have he' : clock - 4 = 8 * CapacityBits.width q +
          (clock - 4 - 8 * CapacityBits.width q) := by omega
      rw [he', natRun_add]
      have hend := (loop_iterations rom q 0 (CapacityBits.width q) built hinit (by omega)).1
      simp only [Nat.zero_add] at hend
      have hendReg := (loop_all_prefixes rom q 0 (CapacityBits.width q) built hb hinit hreg hq hpower
        (by omega) (8 * CapacityBits.width q) le_rfl).1
      exact finish_prefix rom q _ hb hend hendReg hq _ (by omega)

theorem word_refines {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : NatState)
    (hb : 8 ≤ bits) (hf : state.register .fresh = q)
    (hp : state.pc = 0) (ha : state.halted = false) (hr : RegistersFit bits state)
    (hq : Fits bits (q + 1)) (hpower : Fits bits (2 ^ CapacityBits.width q)) :
    packingRun rom program (8 * CapacityBits.width q + 8) (state.toWord bits) =
      (natRun rom program (8 * CapacityBits.width q + 8) state).toWord bits := by
  apply natRun_toWord rom program state _ (code_fit hb)
  intro clock hc
  have hs := all_prefixes rom q state hb hf hp ha hr hq hpower clock hc.le
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  exact ⟨hs.1, hs.2.1.trans_lt (show 60 < 2 ^ bits by omega)⟩

def ofWord {bits : Nat} (state : WordState bits) : NatState :=
  ⟨fun reg => (state.register reg).toNat,
    fun address => (state.heap (BitVec.ofNat bits address)).toNat,
    state.pc.toNat, state.halted⟩

theorem toWord_ofWord {bits : Nat} (state : WordState bits) : (ofWord state).toWord bits = state := by
  apply wordState_ext
  · funext reg
    simp only [ofWord, NatState.toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · funext address
    simp only [ofWord, NatState.toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [ofWord, NatState.toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rfl

theorem actual_word_width {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hf : (state.register .fresh).toNat = q)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (hroom : Fits bits (2 * (q + 1))) :
    let after := packingRun rom program (8 * CapacityBits.width q + 8) state
    after.halted = true ∧ after.register .total = BitVec.ofNat bits (CapacityBits.width q) ∧
      after.register .value = BitVec.ofNat bits (2 ^ CapacityBits.width q) ∧
      after.register .fresh = state.register .fresh ∧ after.heap = state.heap := by
  let lifted := ofWord state
  have hq : Fits bits (q + 1) := by unfold Fits at hroom ⊢; omega
  have hpower : Fits bits (2 ^ CapacityBits.width q) := (power_le q).trans_lt hroom
  have hreg : RegistersFit bits lifted := fun reg => (state.register reg).isLt
  have hlp : lifted.pc = 0 := by simp only [lifted, ofWord, hp, BitVec.toNat_ofNat, Nat.zero_mod]
  have refines := word_refines rom q lifted hb hf hlp ha hreg hq hpower
  rw [show lifted.toWord bits = state from toWord_ofWord state] at refines
  have correct := actual_nat_width rom q lifted hf hlp ha
  dsimp only at correct ⊢
  rw [refines]
  refine ⟨correct.1, ?_, ?_, ?_, ?_⟩
  · change BitVec.ofNat bits _ = _
    rw [correct.2.1]
  · change BitVec.ofNat bits _ = _
    rw [correct.2.2.1]
  · change BitVec.ofNat bits _ = _
    rw [correct.2.2.2.1, ← hf]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change (fun address => BitVec.ofNat bits
      ((natRun rom program (8 * CapacityBits.width q + 8) lifted).heap address.toNat)) = state.heap
    rw [correct.2.2.2.2]
    exact congrArg WordState.heap (toWord_ofWord state)

theorem code_length : (packingCode program).length = 65 := by
  rw [packingCode_length, program_length]

theorem actual_trace_bound {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : WordState bits) :
    (packingDynamicTrace rom program (8 * CapacityBits.width q + 8) state).length ≤
      96 * CapacityBits.width q + 96 := by
  have ht := packingDynamicTrace_length_le rom program (8 * CapacityBits.width q + 8) state
  omega

end PaperProofs.Structure.LaminarTree.PSTRRuntimeWidthRun
