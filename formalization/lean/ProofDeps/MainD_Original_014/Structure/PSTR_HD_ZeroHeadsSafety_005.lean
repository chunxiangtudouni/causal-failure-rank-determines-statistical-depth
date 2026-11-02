module

public import Structure.PSTR_HD_ZeroHeadsFacts_004

/-! Every actual natural prefix of the fixed zero-tool output loop is
bounded and accesses only the original ROM and allocated output words. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRZeroHeads

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

def RegistersBound (N : Nat) (state : NatState) : Prop := ∀ reg, state.register reg ≤ N + 128

def Point (rom : PhysicalROM) (heapWords N : Nat) (state : NatState) : Prop :=
  RegistersBound N state ∧ ∃ index ≤ program.length,
    state.pc = 5 * index ∧
    (state.halted = false → match PackingOp.decode (natFetch program state.pc) with
      | none => natFetch program state.pc = haltWords
      | some op => NatAccessFits rom heapWords state op)

theorem point_body (rom : PhysicalROM) (heapWords N : Nat) (state : NatState)
    (index : Nat) (hi : index < program.length) (hp : state.pc = 5 * index)
    (hr : RegistersBound N state) (ha : NatAccessFits rom heapWords state program[index]) :
    Point rom heapWords N state := by
  refine ⟨hr, index, hi.le, hp, ?_⟩
  intro _
  rw [hp, natFetch_body program index hi, decode_encode]
  exact ha

theorem point_halt (rom : PhysicalROM) (heapWords N : Nat) (state : NatState)
    (hp : state.pc = 115) (hr : RegistersBound N state) : Point rom heapWords N state := by
  refine ⟨hr, 23, by rw [program_length], hp, ?_⟩
  intro _
  rw [hp, show (115 : Nat) = 5 * program.length by rw [program_length], natFetch_halt, decode_halt]

theorem straight_prefix (rom : PhysicalROM) (block : List PackingOp) (start : Nat)
    (hbound : start + block.length ≤ program.length)
    (hcode : ∀ i (hi : i < block.length), program[start + i]'(by omega) = block[i])
    (hstraight : ∀ op ∈ block, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ block.length) :
    natRun rom program count state = runOps rom (block.take count) state := by
  have hl : (block.take count).length = count := List.length_take_of_le hc
  conv_lhs => rw [← hl]
  apply natRun_of_straight_segment rom program (block.take count) start (by omega) ?_ ?_ state hpc ha
  · intro i hi
    have hi' : i < block.length := by rw [hl] at hi; omega
    simpa only [List.getElem_take] using hcode i hi'
  · intro op ho
    exact hstraight op (List.mem_of_mem_take ho)

theorem start_prefix (rom : PhysicalROM) (heap : Nat → Nat) (count : Nat) (hc : count ≤ 12) :
    natRun rom program count (initialNat heap) = runOps rom (startBlock.take count) (initialNat heap) := by
  exact straight_prefix rom startBlock 0 (by decide)
    (by intro i hi; change i < 12 at hi; interval_cases i <;> rfl)
    (by simp [startBlock, NoJump]) (initialNat heap) rfl rfl count hc

theorem test_prefix (rom : PhysicalROM) (heap : Nat → Nat) (N k count : Nat) (hc : count ≤ 2) :
    natRun rom program count (loopState heap N k) = runOps rom (testLead.take count) (loopState heap N k) := by
  exact straight_prefix rom testLead 12 (by decide)
    (by intro i hi; change i < 2 at hi; interval_cases i <;> rfl)
    (by simp [testLead, NoJump]) (loopState heap N k) rfl rfl count hc

theorem body_prefix (rom : PhysicalROM) (heap : Nat → Nat) (N k count : Nat) (hc : count ≤ 5) :
    natRun rom program count (stateAt heap N k (N - k) 105 75) =
      runOps rom (bodyLead.take count) (stateAt heap N k (N - k) 105 75) := by
  exact straight_prefix rom bodyLead 15 (by decide)
    (by intro i hi; change i < 5 at hi; interval_cases i <;> rfl)
    (by simp [bodyLead, NoJump]) (stateAt heap N k (N - k) 105 75) rfl rfl count hc

theorem finish_prefix (rom : PhysicalROM) (heap : Nat → Nat) (N count : Nat) (hc : count ≤ 2) :
    natRun rom program count (stateAt heap N N 0 105 105) =
      runOps rom (finishBlock.take count) (stateAt heap N N 0 105 105) := by
  exact straight_prefix rom finishBlock 21 (by decide)
    (by intro i hi; change i < 2 at hi; interval_cases i <;> rfl)
    (by simp [finishBlock, NoJump]) (stateAt heap N N 0 105 105) rfl rfl count hc

theorem start_point (rom : PhysicalROM) (heap : Nat → Nat) (N heapWords count : Nat)
    (hN : rom.semantic.read .input 0 = N) (hinput : 0 < rom.input.length)
    (hheap : N + 8 ≤ heapWords) (hc : count ≤ 12) :
    Point rom heapWords N (runOps rom (startBlock.take count) (initialNat heap)) := by
  have hdepth : (if N = 0 then 2 else 1) ≤ N + 128 := by split_ifs <;> omega
  have hr : RegistersBound N (runOps rom (startBlock.take count) (initialNat heap)) := by
    intro reg
    cases reg <;> interval_cases count <;>
      simp_all +decide [runOps, startBlock, initialNat, natExecuteOp, Op.execute, Instruction.execute]
  apply point_body rom heapWords N _ count (by rw [program_length]; omega) ?_ hr ?_
  · rw [runOps_pc rom _ _ (fun op ho => (show ∀ op ∈ startBlock, NoJump op from by simp [startBlock, NoJump])
        op (List.mem_of_mem_take ho)), List.length_take_of_le hc]
    simp [initialNat]
  · interval_cases count <;>
      simp_all +decide [NatAccessFits, AccessFits, PhysicalROM.words, runOps, program, startBlock, testLead,
        bodyLead, finishBlock, initialNat, natExecuteOp, Op.execute, Instruction.execute] <;> omega

theorem test_point (rom : PhysicalROM) (heap : Nat → Nat) (N k heapWords count : Nat)
    (hk : k ≤ N) (hc : count ≤ 2) :
    Point rom heapWords N (runOps rom (testLead.take count) (loopState heap N k)) := by
  have hr : RegistersBound N (runOps rom (testLead.take count) (loopState heap N k)) := by
    intro reg
    cases reg <;> interval_cases count <;>
      simp_all +decide [runOps, testLead, loopState, stateAt, natExecuteOp, Op.execute, Instruction.execute] <;> omega
  apply point_body rom heapWords N _ (12 + count) (by rw [program_length]; omega) ?_ hr ?_
  · rw [runOps_pc rom _ _ (fun op ho => (show ∀ op ∈ testLead, NoJump op from by simp [testLead, NoJump])
        op (List.mem_of_mem_take ho)), List.length_take_of_le hc]
    change 60 + 5 * count = 5 * (12 + count)
    omega
  · interval_cases count <;> exact True.intro

theorem body_point (rom : PhysicalROM) (heap : Nat → Nat) (N k heapWords count : Nat)
    (hk : k < N) (hheap : N + 8 ≤ heapWords) (hc : count ≤ 5) :
    Point rom heapWords N (runOps rom (bodyLead.take count) (stateAt heap N k (N - k) 105 75)) := by
  have hr : RegistersBound N (runOps rom (bodyLead.take count) (stateAt heap N k (N - k) 105 75)) := by
    intro reg
    cases reg <;> interval_cases count <;>
      simp_all +decide [runOps, bodyLead, stateAt, natExecuteOp, Op.execute, Instruction.execute] <;> omega
  apply point_body rom heapWords N _ (15 + count) (by rw [program_length]; omega) ?_ hr ?_
  · rw [runOps_pc rom _ _ (fun op ho => (show ∀ op ∈ bodyLead, NoJump op from by simp [bodyLead, NoJump])
        op (List.mem_of_mem_take ho)), List.length_take_of_le hc]
    change 75 + 5 * count = 5 * (15 + count)
    omega
  · interval_cases count <;>
      simp_all +decide [NatAccessFits, AccessFits, runOps, program, startBlock, testLead,
        bodyLead, finishBlock, stateAt, natExecuteOp, Op.execute, Instruction.execute]; omega

theorem finish_point (rom : PhysicalROM) (heap : Nat → Nat) (N heapWords count : Nat)
    (hheap : N + 8 ≤ heapWords) (hc : count ≤ 2) :
    Point rom heapWords N (runOps rom (finishBlock.take count) (stateAt heap N N 0 105 105)) := by
  have hr : RegistersBound N (runOps rom (finishBlock.take count) (stateAt heap N N 0 105 105)) := by
    intro reg
    cases reg <;> interval_cases count <;>
      simp_all +decide [runOps, finishBlock, stateAt, natExecuteOp, Op.execute, Instruction.execute]; omega
  by_cases hlast : count = 2
  · subst count
    apply point_halt rom heapWords N _ rfl hr
  · apply point_body rom heapWords N _ (21 + count) (by rw [program_length]; omega) ?_ hr ?_
    · rw [runOps_pc rom _ _ (fun op ho => (show ∀ op ∈ finishBlock, NoJump op from by simp [finishBlock, NoJump])
          op (List.mem_of_mem_take ho)), List.length_take_of_le hc]
      change 105 + 5 * count = 5 * (21 + count)
      omega
    · have hc' : count ≤ 1 := by omega
      interval_cases count <;>
        simp_all +decide [NatAccessFits, AccessFits, runOps, program, startBlock, testLead,
          bodyLead, finishBlock, stateAt, natExecuteOp, Op.execute, Instruction.execute]; omega

theorem final_point (rom : PhysicalROM) (heap : Nat → Nat) (N heapWords : Nat) :
    Point rom heapWords N (finalState heap N) := by
  apply point_halt rom heapWords N _ rfl
  intro reg
  cases reg <;> simp only [finalState] <;> omega

theorem every_prefix (rom : PhysicalROM) (heap : Nat → Nat) (N heapWords count : Nat)
    (hN : rom.semantic.read .input 0 = N) (hinput : 0 < rom.input.length)
    (hheap : N + 8 ≤ heapWords) (hc : count ≤ 9 * N + 18) :
    Point rom heapWords N (natRun rom program count (initialNat heap)) := by
  by_cases hstart : count ≤ 12
  · rw [start_prefix rom heap count hstart]
    exact start_point rom heap N heapWords count hN hinput hheap hstart
  · have hsplit : count = 12 + (count - 12) := by omega
    rw [hsplit, natRun_add, run_start rom heap N hN]
    by_cases hloop : count - 12 < 9 * N
    · let k := (count - 12) / 9
      let r := (count - 12) % 9
      have hr : r < 9 := Nat.mod_lt _ (by decide)
      have hd : count - 12 = 9 * k + r := by
        have h := Nat.mod_add_div (count - 12) 9
        dsimp only [k, r]
        omega
      have hk : k < N := by omega
      rw [hd, natRun_add, run_iterations rom heap N k hk.le]
      by_cases htest : r ≤ 2
      · rw [test_prefix rom heap N k r htest]
        exact test_point rom heap N k heapWords r hk.le htest
      · have hr' : r = 3 + (r - 3) := by omega
        rw [hr', natRun_add, run_test]
        have hn : N - k ≠ 0 := by omega
        rw [ite_eq_right hn, body_prefix rom heap N k (r - 3) (by omega)]
        exact body_point rom heap N k heapWords (r - 3) hk hheap (by omega)
    · have he : count - 12 = 9 * N + (count - 12 - 9 * N) := by omega
      let r := count - 12 - 9 * N
      have hr : r ≤ 6 := by dsimp only [r]; omega
      rw [he, natRun_add, run_iterations rom heap N N le_rfl]
      change Point rom heapWords N (natRun rom program r (loopState heap N N))
      by_cases htest : r ≤ 2
      · rw [test_prefix rom heap N N r htest]
        exact test_point rom heap N N heapWords r le_rfl htest
      · rw [show r = 3 + (r - 3) by omega, natRun_add, run_test]
        simp only [Nat.sub_self, ↓reduceIte]
        by_cases hfinish : r - 3 ≤ 2
        · rw [finish_prefix rom heap N (r - 3) hfinish]
          exact finish_point rom heap N heapWords (r - 3) hheap hfinish
        · have hlast : r - 3 = 3 := by omega
          rw [hlast]
          have hf := run_exit rom heap N
          rw [show (6 : Nat) = 3 + 3 from rfl, natRun_add, run_test] at hf
          simp only [Nat.sub_self, ↓reduceIte] at hf
          rw [hf]
          exact final_point rom heap N heapWords

end PaperProofs.Structure.LaminarTree.PSTRZeroHeads



