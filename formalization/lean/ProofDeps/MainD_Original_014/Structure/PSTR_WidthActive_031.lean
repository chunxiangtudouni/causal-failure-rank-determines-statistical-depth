module

public import Structure.PSTR_RuntimeWidthRun_007

/-! The actual width loop reaches its continuation ACTIVE before fetching
the standalone HALT. This is the real intermediate state needed by a single
controller program, rather than a fresh invocation of a halted helper. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRWidthActive

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open RawIncidenceLaminarRAM (runOps)
open PSTRRuntimeWidth PSTRRuntimeWidthWord PSTRRuntimeWidthRun

theorem actual_nat_active (rom : PhysicalROM) (q : Nat) (state : NatState)
    (hf : state.register .fresh = q) (hp : state.pc = 0) (ha : state.halted = false) :
    let after := natRun rom program (8 * CapacityBits.width q + 7) state
    after.halted = false ∧ after.pc = 60 ∧ after.register .total = CapacityBits.width q ∧
      after.register .value = 2 ^ CapacityBits.width q ∧
      after.register .fresh = q ∧ after.heap = state.heap := by
  obtain ⟨hinit, hinitFrame⟩ := init_ready rom q state hf hp ha
  let looped := natRun rom program (8 * CapacityBits.width q) (natRun rom program 4 state)
  have iterations := loop_iterations rom q 0 (CapacityBits.width q)
    (natRun rom program 4 state) hinit (by omega)
  have hloop : Ready q (CapacityBits.width q) looped := by
    simpa only [Nat.zero_add] using iterations.1
  have hframe : looped.heap = state.heap := iterations.2.trans hinitFrame
  have hle : q + 1 ≤ 2 ^ CapacityBits.width q := Nat.le_pow_clog (by decide) (q + 1)
  have hz : q + 1 - 2 ^ CapacityBits.width q = 0 := Nat.sub_eq_zero_of_le hle
  dsimp only
  rw [show 8 * CapacityBits.width q + 7 = 4 + (8 * CapacityBits.width q + 3) by omega,
    natRun_add, natRun_add, test_run rom looped hloop.pc hloop.active]
  simp +decide only [testCode, testLead, List.cons_append, List.nil_append, runOps,
    natExecuteOp, Op.execute, Instruction.execute, Function.update_apply, ↓reduceIte,
    hloop.active, hloop.old, hloop.power, hloop.counter, hloop.fresh, hz, hframe, and_self]

theorem actual_word_active {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hf : (state.register .fresh).toNat = q)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (hroom : Fits bits (2 * (q + 1))) :
    let after := packingRun rom program (8 * CapacityBits.width q + 7) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits 60 ∧
      after.register .total = BitVec.ofNat bits (CapacityBits.width q) ∧
      after.register .value = BitVec.ofNat bits (2 ^ CapacityBits.width q) ∧
      after.register .fresh = state.register .fresh ∧ after.heap = state.heap := by
  let lifted := ofWord state
  have hq : Fits bits (q + 1) := by unfold Fits at hroom ⊢; omega
  have hpower : Fits bits (2 ^ CapacityBits.width q) := (power_le q).trans_lt hroom
  have hreg : RegistersFit bits lifted := fun reg => (state.register reg).isLt
  have hlp : lifted.pc = 0 := by simp only [lifted, ofWord, hp, BitVec.toNat_ofNat, Nat.zero_mod]
  have refines := natRun_toWord rom program lifted (8 * CapacityBits.width q + 7) (code_fit hb) (by
    intro clock hc
    have hs := all_prefixes rom q lifted hb hf hlp ha hreg hq hpower clock (by omega)
    have hpow : 256 ≤ 2 ^ bits :=
      (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
    exact ⟨hs.1, hs.2.1.trans_lt (show 60 < 2 ^ bits by omega)⟩)
  rw [show lifted.toWord bits = state from toWord_ofWord state] at refines
  have correct := actual_nat_active rom q lifted hf hlp ha
  dsimp only at correct ⊢
  rw [refines]
  refine ⟨correct.1, ?_, ?_, ?_, ?_, ?_⟩
  · change BitVec.ofNat bits _ = _
    rw [correct.2.1]
  · change BitVec.ofNat bits _ = _
    rw [correct.2.2.1]
  · change BitVec.ofNat bits _ = _
    rw [correct.2.2.2.1]
  · change BitVec.ofNat bits _ = _
    rw [correct.2.2.2.2.1, ← hf]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change (fun address => BitVec.ofNat bits
      ((natRun rom program (8 * CapacityBits.width q + 7) lifted).heap address.toNat)) = state.heap
    rw [correct.2.2.2.2.2]
    exact congrArg WordState.heap (toWord_ofWord state)

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : WordState bits) :
    (packingDynamicTrace rom program (8 * CapacityBits.width q + 7) state).length ≤
      96 * CapacityBits.width q + 84 := by
  have ht := packingDynamicTrace_length_le rom program (8 * CapacityBits.width q + 7) state
  omega

end PaperProofs.Structure.LaminarTree.PSTRWidthActive
