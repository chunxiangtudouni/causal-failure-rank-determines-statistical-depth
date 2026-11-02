module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009b

/-! Runtime clear-loop induction. `clearHeap` is only the mathematical final
heap specification; it is never supplied to the executable controller. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def clearHeap {bits : Nat} (base : Nat) : Nat → (BitVec bits → BitVec bits) → (BitVec bits → BitVec bits)
  | 0, heap => heap
  | count + 1, heap => Function.update (clearHeap base count heap)
      (BitVec.ofNat bits (base + count)) (BitVec.ofNat bits 0)

structure ClearReady {bits : Nat} (origin header base done remaining : Nat)
    (heap : BitVec bits → BitVec bits) (state : WordState bits) : Prop where
  address : state.register .address = BitVec.ofNat bits header
  index : state.register .index = BitVec.ofNat bits (base + done)
  total : state.register .total = BitVec.ofNat bits remaining
  value : state.register .value = BitVec.ofNat bits 0
  flag : state.register .flag = BitVec.ofNat bits 1
  memory : state.heap = clearHeap base done heap
  pc : state.pc = BitVec.ofNat bits (5 * (origin + 14))
  active : state.halted = false

theorem clear_ready_setup {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (q size header : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hq : (rom.words .input).getD 1 0 = q) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    ClearReady origin header (childBase header q) 0 (size + 1) state.heap (packingRun rom containing 14 state) := by
  rw [fetched_clear_setup em rom state hp ha]
  have hs := clearSetup_result rom q size header state h1 hsize hq hh
  rcases hs with ⟨had, ht, _, hi, hv, hf, hm⟩
  refine ⟨had, ?_, ht, hv, hf, hm, ?_, ?_⟩
  · simpa only [Nat.add_zero] using hi
  · rw [executeOps_pc rom clearSetup state clearSetup_straight, hp, clearSetup_length, BitVec.ofNat_add_ofNat]
    congr 1
  · rw [executeOps_halted, ha]

theorem clear_iteration {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (header base done remaining : Nat)
    (heap : BitVec bits → BitVec bits) (state : WordState bits)
    (h1 : Fits bits 1) (hr : Fits bits (remaining + 1))
    (ready : ClearReady origin header base done (remaining + 1) heap state) :
    ClearReady origin header base (done + 1) remaining heap (packingRun rom containing 7 state) := by
  let tested := executeOps rom (clearTest origin) state
  have ht := clear_test_result rom origin (remaining + 1) state ready.pc ready.total hr
  have hpc : tested.pc = BitVec.ofNat bits (5 * (origin + 16)) := by
    simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
  have hactive : tested.halted = false := by rw [executeOps_halted, ready.active]
  have hreg (r : Register) (hn : r ≠ .old) : tested.register r = state.register r :=
    clear_test_register rom origin state r hn
  have hb := clearBody_result rom origin remaining (base + done) tested h1 hr
    ((hreg .index (by decide)).trans ready.index) ((hreg .total (by decide)).trans ready.total)
    ((hreg .value (by decide)).trans ready.value) ((hreg .flag (by decide)).trans ready.flag)
  have hrun : packingRun rom containing 7 state = executeOps rom (clearBody origin) tested := by
    rw [show 7 = 2 + 5 from rfl, run_add, fetched_clear_test em rom state ready.pc ready.active]
    exact fetched_clear_body em rom tested hpc hactive
  rw [hrun]
  refine ⟨hb.2.2.2.1.trans ((hreg .address (by decide)).trans ready.address), ?_, hb.2.2.1,
    hb.2.2.2.2.1, hb.2.2.2.2.2.1, ?_, hb.2.2.2.2.2.2, ?_⟩
  · simpa only [Nat.add_assoc] using hb.2.1
  · rw [hb.1, ht.2, ready.memory]
    rfl
  · rw [executeOps_halted, hactive]

theorem clear_iterations {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (header base done remaining iterations : Nat)
    (heap : BitVec bits → BitVec bits) (state : WordState bits)
    (h1 : Fits bits 1) (hr : Fits bits (remaining + iterations))
    (ready : ClearReady origin header base done (remaining + iterations) heap state) :
    ClearReady origin header base (done + iterations) remaining heap
      (packingRun rom containing (7 * iterations) state) := by
  induction iterations generalizing done state with
  | zero => simpa only [Nat.add_zero, Nat.mul_zero, packingRun] using ready
  | succ iterations ih =>
    have hr' : Fits bits ((remaining + iterations) + 1) := by simpa only [Nat.add_assoc] using hr
    have rd : ClearReady origin header base done ((remaining + iterations) + 1) heap state := by
      simpa only [Nat.add_assoc] using ready
    have next := clear_iteration em rom header base done (remaining + iterations) heap state h1 hr' rd
    rw [show 7 * (iterations + 1) = 7 + 7 * iterations by omega, run_add]
    have hind := ih (done + 1) _ ((Nat.le_succ _).trans_lt hr') next
    simpa only [Nat.add_assoc, Nat.add_comm 1 iterations] using hind

theorem actual_clear_kernel {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (q size header : Nat) (state : WordState bits)
    (hroom : Fits bits (childBase header q + size + 1))
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hq : (rom.words .input).getD 1 0 = q) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let after := packingRun rom containing (clearSteps size) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 21)) ∧
      after.heap = clearHeap (childBase header q) (size + 1) state.heap ∧
      after.register .address = BitVec.ofNat bits header ∧
      after.register .index = BitVec.ofNat bits (childBase header q + size + 1) ∧
      after.register .total = BitVec.ofNat bits 0 ∧ after.register .value = BitVec.ofNat bits 0 ∧
      after.register .flag = BitVec.ofNat bits 1 := by
  have h1 : Fits bits 1 := (show 1 ≤ childBase header q + size + 1 by omega).trans_lt hroom
  have hsf : Fits bits (size + 1) := (show size + 1 ≤ childBase header q + size + 1 by omega).trans_lt hroom
  let a := packingRun rom containing 14 state
  let looped := packingRun rom containing (7 * (size + 1)) a
  have hinit := clear_ready_setup em rom q size header state h1 hsize hq hh hp ha
  have hend : ClearReady origin header (childBase header q) (size + 1) 0 state.heap looped := by
    simpa only [Nat.zero_add] using clear_iterations em rom header (childBase header q) 0 0 (size + 1) state.heap a h1
      (by simpa only [Nat.zero_add] using hsf) (by simpa only [Nat.zero_add] using hinit)
  have ht := clear_test_result rom origin 0 looped hend.pc hend.total ((show 0 ≤ 1 by decide).trans_lt h1)
  have hrun : packingRun rom containing (clearSteps size) state = executeOps rom (clearTest origin) looped := by
    rw [show clearSteps size = 14 + 7 * (size + 1) + 2 by unfold clearSteps; omega, run_add, run_add]
    exact fetched_clear_test em rom looped hend.pc hend.active
  have hreg (r : Register) (hn : r ≠ .old) :
      (executeOps rom (clearTest origin) looped).register r = looped.register r := clear_test_register rom origin looped r hn
  rw [hrun]
  refine ⟨by rw [executeOps_halted, hend.active], ?_, ht.2.trans hend.memory,
    (hreg .address (by decide)).trans hend.address, ?_,
    (hreg .total (by decide)).trans hend.total, (hreg .value (by decide)).trans hend.value,
    (hreg .flag (by decide)).trans hend.flag⟩
  · simpa only [ite_true] using ht.1
  · simpa only [Nat.add_assoc] using (hreg .index (by decide)).trans hend.index

theorem clearHeap_frame {bits : Nat} (base count : Nat) (heap : BitVec bits → BitVec bits) (address : BitVec bits)
    (hne : ∀ i < count, address ≠ BitVec.ofNat bits (base + i)) : clearHeap base count heap address = heap address := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [clearHeap, Function.update_of_ne (hne count (by omega))]
    exact ih (by intro i hi; exact hne i (by omega))

theorem clearHeap_zero {bits : Nat} (base count : Nat) (heap : BitVec bits → BitVec bits)
    (hfit : Fits bits (base + count)) (i : Nat) (hi : i < count) :
    clearHeap base count heap (BitVec.ofNat bits (base + i)) = BitVec.ofNat bits 0 := by
  induction count with
  | zero => omega
  | succ count ih =>
    by_cases he : i = count
    · subst i
      simp only [clearHeap, Function.update_self]
    · have hil : i < count := by omega
      have hf1 : Fits bits (base + i) := (show base + i ≤ base + (count + 1) by omega).trans_lt hfit
      have hf2 : Fits bits (base + count) := (show base + count ≤ base + (count + 1) by omega).trans_lt hfit
      have hne : BitVec.ofNat bits (base + i) ≠ BitVec.ofNat bits (base + count) := by
        apply (ofNat_injective_of_fit _ _ hf1 hf2).not.mpr
        omega
      rw [clearHeap, Function.update_of_ne hne]
      exact ih hf2 hil

theorem actual_clear_trace_le {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (size : Nat) (state : WordState bits) :
    (packingDynamicTrace rom containing (clearSteps size) state).length ≤ 276 * (size + 1) := by
  have hh := packingDynamicTrace_length_le rom containing (clearSteps size) state
  unfold clearSteps at hh ⊢
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
