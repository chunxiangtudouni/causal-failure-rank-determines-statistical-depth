module

public import PaperProofs.Structure.PSTR_WidthKernel_032
public import PaperProofs.Structure.PackedCapacityRAM

/-! The actual containing program computes width and then its mask from q.
Neither is an input answer. The loop and the following subtraction remain
ACTIVE, with the same heap and literal containing-program continuation. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRWidthEmbedded

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PSTRWidthKernel

theorem power_room {bits : Nat} (q k : Nat) (hroom : Fits bits (2 * (q + 1)))
    (hk : k ≤ CapacityBits.width q) : Fits bits (2 ^ k) :=
  ((Nat.pow_le_pow_right (by decide) hk).trans (PSTRRuntimeWidthWord.power_le q)).trans_lt hroom

theorem loop_step {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (q k : Nat) (state : WordState bits)
    (hs : Ready q k start state) (hroom : Fits bits (2 * (q + 1))) (hk : k < CapacityBits.width q) :
    Ready q (k + 1) start (packingRun rom whole 8 state) ∧
      (packingRun rom whole 8 state).heap = state.heap := by
  have hq : Fits bits (q + 1) := by unfold Fits at hroom ⊢; omega
  have hpow := power_room q k hroom hk.le
  have hlt : 2 ^ k < q + 1 := Nat.pow_lt_of_lt_clog hk
  have hne : q + 1 - 2 ^ k ≠ 0 := by omega
  let tested := executeOps rom (testAt start) state
  have hd : Data q k tested := test_data rom q k start state hs.toData
  have hp : tested.pc = BitVec.ofNat bits (5 * (start + 7)) := by
    rw [test_pc rom q k start state hs hq hpow, ite_eq_right hne]
  have ha : tested.halted = false := by rw [executeOps_halted, hs.active]
  rw [show 8 = 3 + 5 from rfl, PSTRWordSegments.run_add,
    test_run rom whole start hc hw hpcfit state hs.pc hs.active,
    body_run rom whole start hc hw hpcfit tested hp ha]
  exact ⟨body_ready rom q k start tested hd ha, (body_heap rom start tested).trans (test_heap rom start state)⟩

theorem iterations {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (q k count : Nat) (state : WordState bits)
    (hs : Ready q k start state) (hroom : Fits bits (2 * (q + 1)))
    (hk : k + count ≤ CapacityBits.width q) :
    Ready q (k + count) start (packingRun rom whole (8 * count) state) ∧
      (packingRun rom whole (8 * count) state).heap = state.heap := by
  induction count generalizing k state with
  | zero => simpa only [Nat.add_zero, Nat.mul_zero, packingRun] using And.intro hs (rfl : state.heap = state.heap)
  | succ count ih =>
    obtain ⟨hnext, hframe⟩ := loop_step rom whole start hc hw hpcfit q k state hs hroom (by omega)
    obtain ⟨hfinal, hlast⟩ := ih (k + 1) (packingRun rom whole 8 state) hnext (by omega)
    rw [show 8 * (count + 1) = 8 + 8 * count by omega, PSTRWordSegments.run_add]
    refine ⟨?_, hlast.trans hframe⟩
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using hfinal

theorem actual_width {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (q : Nat) (state : WordState bits)
    (hf : (state.register .fresh).toNat = q)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hroom : Fits bits (2 * (q + 1))) :
    let after := packingRun rom whole (8 * CapacityBits.width q + 7) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (start + 12)) ∧
      Data q (CapacityBits.width q) after ∧ after.heap = state.heap := by
  have hinit : Ready q 0 start (packingRun rom whole 4 state) := by
    rw [init_run rom whole start hc hw hpcfit state hp ha]
    exact init_ready rom q start state hf hp ha
  have hinitFrame : (packingRun rom whole 4 state).heap = state.heap := by
    rw [init_run rom whole start hc hw hpcfit state hp ha]
    exact init_heap rom state
  have hloop := iterations rom whole start hc hw hpcfit q 0 (CapacityBits.width q)
    (packingRun rom whole 4 state) hinit hroom (by omega)
  simp only [Nat.zero_add] at hloop
  let looped := packingRun rom whole (8 * CapacityBits.width q) (packingRun rom whole 4 state)
  have hs : Ready q (CapacityBits.width q) start looped := hloop.1
  have hq : Fits bits (q + 1) := by unfold Fits at hroom ⊢; omega
  have hpow := power_room q (CapacityBits.width q) hroom le_rfl
  have hle : q + 1 ≤ 2 ^ CapacityBits.width q := Nat.le_pow_clog (by decide) (q + 1)
  have hz : q + 1 - 2 ^ CapacityBits.width q = 0 := Nat.sub_eq_zero_of_le hle
  dsimp only
  rw [show 8 * CapacityBits.width q + 7 = 4 + (8 * CapacityBits.width q + 3) by omega,
    PSTRWordSegments.run_add, PSTRWordSegments.run_add,
    test_run rom whole start hc hw hpcfit looped hs.pc hs.active]
  refine ⟨?_, ?_, test_data rom q _ start looped hs.toData, ?_⟩
  · rw [executeOps_halted, hs.active]
  · rw [test_pc rom q _ start looped hs hq hpow, ite_eq_left hz]
  · exact (test_heap rom start looped).trans (hloop.2.trans hinitFrame)

def maskOp : PackingOp := .base (.subtract .flag .value .index)

theorem mask_data {bits : Nat} (rom : PhysicalROM) (q k : Nat) (state : WordState bits)
    (hs : Data q k state) : Data q k (packingExecuteOp rom maskOp state) :=
  ⟨hs.fresh, hs.old, hs.power, hs.counter, hs.one⟩

theorem mask_value {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : WordState bits)
    (hs : Data q (CapacityBits.width q) state) (hroom : Fits bits (2 * (q + 1))) :
    (packingExecuteOp rom maskOp state).register .flag = lowMask bits (CapacityBits.width q) := by
  have hp := power_room q (CapacityBits.width q) hroom le_rfl
  have hone : 1 < 2 ^ bits := by unfold Fits at hroom; omega
  simp +decide only [maskOp, packingExecuteOp, wordOp, Function.update_self,
    hs.power, hs.one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hone, lowMask]

theorem actual_width_mask {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length))
    (hbound : start + 13 ≤ whole.length)
    (hmask : whole[start + 12]'(by omega) = maskOp)
    (q : Nat) (state : WordState bits) (hf : (state.register .fresh).toNat = q)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hroom : Fits bits (2 * (q + 1))) :
    let after := packingRun rom whole (8 * CapacityBits.width q + 8) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (start + 13)) ∧
      Data q (CapacityBits.width q) after ∧
      after.register .flag = lowMask bits (CapacityBits.width q) ∧ after.heap = state.heap := by
  let count := 8 * CapacityBits.width q + 7
  let current := packingRun rom whole count state
  have result := actual_width rom whole start hc hw hpcfit q state hf hp ha hroom
  have hpc : current.pc.toNat = 5 * (start + 12) := by
    rw [result.2.1, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 (by omega)).trans_lt hpcfit)
  dsimp only
  rw [show 8 * CapacityBits.width q + 8 = count + 1 from rfl, packingRun_succ,
    packingStep_of_index rom whole current (start + 12) (by omega) hw hpc result.1, hmask]
  refine ⟨?_, ?_, mask_data rom q _ current result.2.2.1,
    mask_value rom q current result.2.2.1 hroom, ?_⟩
  · exact result.1
  · change current.pc + BitVec.ofNat bits 5 = _
    rw [result.2.1, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat bits) (show 5 * (start + 12) + 5 = 5 * (start + 13) by omega)
  · exact result.2.2.2

theorem trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (q : Nat) (state : WordState bits) :
    (packingDynamicTrace rom whole (8 * CapacityBits.width q + 8) state).length ≤
      96 * CapacityBits.width q + 96 := by
  have ht := packingDynamicTrace_length_le rom whole (8 * CapacityBits.width q + 8) state
  omega

end PaperProofs.Structure.LaminarTree.PSTRWidthEmbedded
