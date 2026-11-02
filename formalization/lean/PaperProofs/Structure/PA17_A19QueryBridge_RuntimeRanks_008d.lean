module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeRanks_008c

/-! Real runtime reverse-loop invariant and the complete ACTIVE rank kernel.
The arrays describe flags produced inside the controller's same run; no such
arrays, rank values, traces or safety certificates are new A19 caller data. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments

structure Ready {bits : Nat} (origin q header remaining : Nat) (good bad : Nat → Bool)
    (heap : BitVec bits → BitVec bits) (state : WordState bits) : Prop where
  bound : remaining ≤ q + 2
  address : state.register .address = BitVec.ofNat bits header
  total : state.register .total = BitVec.ofNat bits (q + 2)
  index : state.register .index = BitVec.ofNat bits remaining
  goodValue : state.register .value = BitVec.ofNat bits (suffix q remaining good)
  badValue : state.register .fresh = BitVec.ofNat bits (suffix q remaining bad)
  memory : state.heap = heap
  pc : state.pc = BitVec.ofNat bits (5 * (origin + 8))
  active : state.halted = false

theorem test_register {bits : Nat} (rom : PhysicalROM) (origin : Nat) (state : WordState bits)
    (register : Register) (hne : register ≠ .old) :
    (executeOps rom (testBlock origin) state).register register = state.register register := by
  cases register <;> try rfl
  exact False.elim (hne rfl)

theorem ready_setup {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (q header : Nat) (good bad : Nat → Bool) (state : WordState bits)
    (h1 : Fits bits 1) (hq : (rom.words .input).getD 1 0 = q)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    Ready origin q header (q + 2) good bad state.heap (packingRun rom containing 8 state) := by
  rw [fetched_setup em rom state hp ha]
  have hs := execute_setup rom q state h1 hq
  refine ⟨le_rfl, hs.1.trans hh, hs.2.1, hs.2.2.1, ?_, ?_, hs.2.2.2.2.2, ?_, ?_⟩
  · simpa only [suffix_init] using hs.2.2.2.1
  · simpa only [suffix_init] using hs.2.2.2.2.1
  · rw [executeOps_pc rom setup state setup_straight, hp, setup_length, BitVec.ofNat_add_ofNat]
    congr 1
  · rw [executeOps_halted, ha]

theorem fetched_iteration {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (q header remaining : Nat) (good bad : Nat → Bool)
    (heap : BitVec bits → BitVec bits) (state : WordState bits)
    (h1 : Fits bits 1) (hqf : Fits bits (q + 2))
    (hgood : ∀ budget < q + 2, heap (BitVec.ofNat bits (header + 16 + budget)) = BitVec.ofNat bits (bit (good budget)))
    (hbad : ∀ budget < q + 2, heap (BitVec.ofNat bits (header + 16 + budget + (q + 2))) = BitVec.ofNat bits (bit (bad budget)))
    (ready : Ready origin q header (remaining + 1) good bad heap state) :
    Ready origin q header remaining good bad heap (packingRun rom containing 15 state) := by
  have hr : Fits bits (remaining + 1) := ready.bound.trans_lt hqf
  let tested := executeOps rom (testBlock origin) state
  have ht := execute_test rom origin (remaining + 1) state ready.pc ready.index hr
  have hpc : tested.pc = BitVec.ofNat bits (5 * (origin + 10)) := by simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
  have hactive : tested.halted = false := by rw [executeOps_halted, ready.active]
  have hreg (register : Register) (hne : register ≠ .old) : tested.register register = state.register register :=
    test_register rom origin state register hne
  have hb := execute_body rom origin q header remaining (suffix q (remaining + 1) good) (suffix q (remaining + 1) bad)
    tested h1 hr ((hreg .address (by decide)).trans ready.address) ((hreg .index (by decide)).trans ready.index)
    ((hreg .total (by decide)).trans ready.total) ((hreg .value (by decide)).trans ready.goodValue)
    ((hreg .fresh (by decide)).trans ready.badValue)
  rcases hb with ⟨haddr, htotal, hindex, hgv, hbv, hmemory, hback⟩
  have hloadGood : tested.heap (BitVec.ofNat bits (header + 16 + remaining)) = BitVec.ofNat bits (bit (good remaining)) := by
    rw [ht.2, ready.memory]
    exact hgood remaining (by have hh := ready.bound; omega)
  have hloadBad : tested.heap (BitVec.ofNat bits (header + 16 + remaining + (q + 2))) = BitVec.ofNat bits (bit (bad remaining)) := by
    rw [ht.2, ready.memory]
    exact hbad remaining (by have hh := ready.bound; omega)
  have hrun : packingRun rom containing 15 state = executeOps rom (bodyBlock origin) tested := by
    rw [show 15 = 2 + 13 from rfl, run_add, fetched_test em rom state ready.pc ready.active]
    exact fetched_body em rom tested hpc hactive
  rw [hrun]
  refine ⟨by have hh := ready.bound; omega, haddr, htotal, hindex, ?_, ?_, ?_, hback, ?_⟩
  · rw [hgv, hloadGood, suffix_step q remaining good (by have hh := ready.bound; omega)]
    cases good remaining <;> simp [bit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
  · rw [hbv, hloadBad, suffix_step q remaining bad (by have hh := ready.bound; omega)]
    cases bad remaining <;> simp [bit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
  · exact hmemory.trans (ht.2.trans ready.memory)
  · rw [executeOps_halted, hactive]

theorem fetched_iterations {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (q header remaining iterations : Nat) (good bad : Nat → Bool)
    (heap : BitVec bits → BitVec bits) (state : WordState bits)
    (h1 : Fits bits 1) (hqf : Fits bits (q + 2))
    (hgood : ∀ budget < q + 2, heap (BitVec.ofNat bits (header + 16 + budget)) = BitVec.ofNat bits (bit (good budget)))
    (hbad : ∀ budget < q + 2, heap (BitVec.ofNat bits (header + 16 + budget + (q + 2))) = BitVec.ofNat bits (bit (bad budget)))
    (ready : Ready origin q header (remaining + iterations) good bad heap state) :
    Ready origin q header remaining good bad heap (packingRun rom containing (15 * iterations) state) := by
  induction iterations generalizing state with
  | zero => simpa only [Nat.add_zero, Nat.mul_zero, packingRun] using ready
  | succ iterations ih =>
    have hr : Ready origin q header ((remaining + iterations) + 1) good bad heap state := by
      simpa only [Nat.add_assoc] using ready
    have next := fetched_iteration em rom q header (remaining + iterations) good bad heap state h1 hqf hgood hbad hr
    rw [show 15 * (iterations + 1) = 15 + 15 * iterations by omega, run_add]
    exact ih _ next

theorem actual_kernel {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (q header : Nat) (good bad : Nat → Bool) (state : WordState bits)
    (hroom : Fits bits (header + 16 + 2 * (q + 2)))
    (hq : (rom.words .input).getD 1 0 = q)
    (hgood : ∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget)) = BitVec.ofNat bits (bit (good budget)))
    (hbad : ∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget + (q + 2))) = BitVec.ofNat bits (bit (bad budget)))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let after := packingRun rom containing (steps q) state
    let g := PA17QueryRanks011.firstFalseValue q good
    let b := PA17QueryRanks011.firstFalseValue q bad
    let active := (state.heap (BitVec.ofNat bits (header + 2))).toNat
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 51)) ∧
      after.heap = resultHeap header g b state.heap ∧
      after.register .old = BitVec.ofNat bits (if active = 0 then q + 2 else g) ∧
      after.register .fresh = BitVec.ofNat bits (if active = 0 then 0 else b) ∧
      after.register .value = BitVec.ofNat bits (if active = 0 then q + 2 else min g (b + 1)) ∧
      after.register .index = BitVec.ofNat bits 0 ∧ after.register .address = BitVec.ofNat bits header := by
  have h1 : Fits bits 1 := (show 1 ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  have hqf : Fits bits (q + 2) := (show q + 2 ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  let a := packingRun rom containing 8 state
  let looped := packingRun rom containing (15 * (q + 2)) a
  let tested := executeOps rom (testBlock origin) looped
  have hinit := ready_setup em rom q header good bad state h1 hq hh hp ha
  have hend : Ready origin q header 0 good bad state.heap looped := by
    simpa only [Nat.zero_add] using fetched_iterations em rom q header 0 (q + 2) good bad state.heap a h1 hqf hgood hbad
      (by simpa only [Nat.zero_add] using hinit)
  have htest := execute_test rom origin 0 looped hend.pc hend.index ((show 0 ≤ 1 by decide).trans_lt h1)
  have htestpc : tested.pc = BitVec.ofNat bits (5 * (origin + 23)) := by simpa only [ite_true] using htest.1
  have htestactive : tested.halted = false := by rw [executeOps_halted, hend.active]
  have hreg (register : Register) (hne : register ≠ .old) : tested.register register = looped.register register :=
    test_register rom origin looped register hne
  have hmem : tested.heap = state.heap := htest.2.trans hend.memory
  have hf := execute_footer rom q header (suffix q 0 good) (suffix q 0 bad) tested hroom
    (suffix_bound q 0 good) (suffix_bound q 0 bad)
    ((hreg .address (by decide)).trans hend.address) ((hreg .value (by decide)).trans hend.goodValue)
    ((hreg .fresh (by decide)).trans hend.badValue) ((hreg .total (by decide)).trans hend.total)
  rw [hmem] at hf
  simp only [suffix_final] at hf
  have hrun : packingRun rom containing (steps q) state = executeOps rom footer tested := by
    rw [show steps q = 8 + 15 * (q + 2) + 2 + 28 by unfold steps; omega,
      run_add, run_add, run_add, fetched_test em rom looped hend.pc hend.active]
    exact fetched_footer em rom tested htestpc htestactive
  rw [hrun]
  refine ⟨?_, ?_, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2⟩
  · rw [executeOps_halted, htestactive]
  · rw [executeOps_pc rom footer tested footer_straight, htestpc, footer_length, BitVec.ofNat_add_ofNat]
    congr 1

theorem actual_trace_le {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (q : Nat) (state : WordState bits) :
    (packingDynamicTrace rom containing (steps q) state).length ≤ 816 * (q + 1) := by
  have hh := packingDynamicTrace_length_le rom containing (steps q) state
  unfold steps at hh ⊢
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008
