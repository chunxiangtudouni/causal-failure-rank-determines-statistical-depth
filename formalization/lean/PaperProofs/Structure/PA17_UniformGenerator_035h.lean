module

public import PaperProofs.Structure.PA17_UniformGenerator_035g

/-! A real finite divide-by-two/count loop for the two logarithms needed
by packed code generation. No clog or width value is an ISA primitive. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035h

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035g

theorem clog_half (value : Nat) (hv : 0 < value) :
    Nat.clog 2 (value + 1) = Nat.clog 2 (value / 2 + 1) + 1 := by
  rw [Nat.clog_of_two_le (by decide : 1 < 2) (show 2 ≤ value + 1 by omega)]
  congr 2
  omega

def logInit : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.constant .fresh 2)),
   .base (.base (.constant .total 1)), .base (.base (.constant .flag 0))]

def logHead (exit : Nat) : List PackingOp :=
  [.base (.base (.constant .old exit)), .jumpIfZero .value .old]

def logTail (entry : Nat) : List PackingOp :=
  [.arithmetic .divide .value .value .fresh, .base (.base (.add .index .index .total)),
   .base (.base (.constant .old entry)), .jumpIfZero .flag .old]

def logBlock (start : Nat) : List PackingOp :=
  logInit ++ logHead (5 * (start + 10)) ++ logTail (5 * (start + 4))

theorem logBlock_length (start : Nat) : (logBlock start).length = 10 := rfl

theorem log_init_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ logBlock left.length ++ right) 4 state = runOps rom logInit state := by
  have hlen : logInit.length = 4 := rfl
  have hh := natRun_of_straight_segment rom
    (left ++ logInit ++ (logHead (5 * (left.length + 10)) ++ logTail (5 * (left.length + 4)) ++ right)) logInit left.length
    (by simp only [List.length_append]; omega)
    (segment_index left logInit _) (by simp [logInit, NoJump]) state hpc ha
  simpa only [logBlock, List.append_assoc, hlen] using hh

theorem log_head_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 4)) (ha : state.halted = false) :
    natRun rom (left ++ logBlock left.length ++ right) 2 state = runOps rom (logHead (5 * (left.length + 10))) state := by
  have hp : (left ++ logInit).length = left.length + 4 := by simp [logInit]
  have hh := branch_segment_run rom (left ++ logInit)
    [.base (.base (.constant .old (5 * (left.length + 10))))] (logTail (5 * (left.length + 4)) ++ right)
    (.jumpIfZero .value .old) (by simp [NoJump]) state (by rw [hp]; exact hpc) ha
  simpa only [logBlock, logHead, List.append_assoc, List.length_singleton, List.singleton_append] using hh

theorem log_tail_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 6)) (ha : state.halted = false) :
    natRun rom (left ++ logBlock left.length ++ right) 4 state = runOps rom (logTail (5 * (left.length + 4))) state := by
  let lead := (logTail (5 * (left.length + 4))).take 3
  have hp : (left ++ logInit ++ logHead (5 * (left.length + 10))).length = left.length + 6 := by simp [logInit, logHead]
  have hh := branch_segment_run rom (left ++ logInit ++ logHead (5 * (left.length + 10)))
    lead right (.jumpIfZero .flag .old) (by simp [lead, logTail, NoJump]) state (by rw [hp]; exact hpc) ha
  simpa only [logBlock, logTail, lead, List.take_succ_cons, List.take_zero, List.append_assoc,
    List.cons_append, List.nil_append, List.length_cons, List.length_nil] using hh

def LogInv (offset value : Nat) (state : NatState) : Prop :=
  state.register .index = offset ∧ state.register .value = value ∧ state.register .fresh = 2 ∧
    state.register .total = 1 ∧ state.register .flag = 0

theorem log_init_inv (rom : PhysicalROM) (state : NatState) : LogInv 0 (state.register .value) (runOps rom logInit state) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem log_head_inv (rom : PhysicalROM) (exit offset value : Nat) (state : NatState) (hi : LogInv offset value state) :
    LogInv offset value (runOps rom (logHead exit) state) := hi

theorem log_tail_inv (rom : PhysicalROM) (entry offset value : Nat) (state : NatState) (hi : LogInv offset value state) :
    LogInv (offset + 1) (value / 2) (runOps rom (logTail entry) state) := by
  rcases hi with ⟨hindex, hvalue, hfresh, htotal, hflag⟩
  refine ⟨?_, ?_, hfresh, htotal, hflag⟩
  · change state.register .index + state.register .total = offset + 1
    rw [hindex, htotal]
  · change state.register .value / state.register .fresh = value / 2
    rw [hvalue, hfresh]

theorem log_head_pc (rom : PhysicalROM) (exit : Nat) (state : NatState) :
    (runOps rom (logHead exit) state).pc = if state.register .value = 0 then exit else state.pc + 10 := by
  simp [logHead, runOps, natExecuteOp, Op.execute, Instruction.execute, Nat.add_assoc]

theorem log_tail_pc (rom : PhysicalROM) (entry : Nat) (state : NatState) (hz : state.register .flag = 0) :
    (runOps rom (logTail entry) state).pc = entry := by
  simp [logTail, runOps, natExecuteOp, Op.execute, Instruction.execute, hz]

theorem log_loop_run (rom : PhysicalROM) (left right : List PackingOp) (value offset : Nat) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 4)) (ha : state.halted = false) (hi : LogInv offset value state) :
    let fresh := natRun rom (left ++ logBlock left.length ++ right) (6 * Nat.clog 2 (value + 1) + 2) state
    LogInv (offset + Nat.clog 2 (value + 1)) 0 fresh ∧ fresh.pc = 5 * (left.length + 10) ∧
      fresh.halted = false ∧ fresh.heap = state.heap := by
  induction value using Nat.strong_induction_on generalizing offset state with
  | h value ih =>
    by_cases hv : value = 0
    · subst value
      simp only [Nat.zero_add, Nat.clog_one_right, Nat.mul_zero, Nat.add_zero]
      rw [log_head_run rom left right state hpc ha]
      refine ⟨log_head_inv rom _ offset 0 state hi, ?_, (runOps_halted rom _ state).trans ha, rfl⟩
      rw [log_head_pc, hi.2.1, ite_eq_left rfl]
    · let tested := runOps rom (logHead (5 * (left.length + 10))) state
      have htest := log_head_inv rom (5 * (left.length + 10)) offset value state hi
      have htpc : tested.pc = 5 * (left.length + 6) := by
        rw [log_head_pc, hi.2.1, ite_eq_right hv, hpc]
        omega
      have hta : tested.halted = false := (runOps_halted rom _ state).trans ha
      let divided := runOps rom (logTail (5 * (left.length + 4))) tested
      have hd := log_tail_inv rom (5 * (left.length + 4)) offset value tested htest
      have hdpc : divided.pc = 5 * (left.length + 4) := log_tail_pc rom _ tested htest.2.2.2.2
      have hda : divided.halted = false := (runOps_halted rom _ tested).trans hta
      have hsmall : value / 2 < value := Nat.div_lt_self (by omega) (by decide)
      have hr := ih (value / 2) hsmall (offset + 1) divided hdpc hda hd
      have htime : 6 * Nat.clog 2 (value + 1) + 2 = (2 + 4) + (6 * Nat.clog 2 (value / 2 + 1) + 2) := by
        rw [clog_half value (by omega)]
        omega
      have hcycle : natRun rom (left ++ logBlock left.length ++ right) (2 + 4) state = divided := by
        rw [natRun_add, log_head_run rom left right state hpc ha, log_tail_run rom left right tested htpc hta]
      rw [htime, natRun_add, hcycle]
      have hindex : offset + Nat.clog 2 (value + 1) = offset + 1 + Nat.clog 2 (value / 2 + 1) := by
        rw [clog_half value (by omega)]
        omega
      rw [hindex]
      refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_⟩
      exact hr.2.2.2

theorem log_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    let fresh := natRun rom (left ++ logBlock left.length ++ right) (6 * Nat.clog 2 (state.register .value + 1) + 6) state
    LogInv (Nat.clog 2 (state.register .value + 1)) 0 fresh ∧ fresh.pc = 5 * (left.length + 10) ∧
      fresh.halted = false ∧ fresh.heap = state.heap := by
  let prepared := runOps rom logInit state
  have hp : prepared.pc = 5 * (left.length + 4) := by
    rw [runOps_pc rom _ state (by simp [logInit, NoJump]), hpc]
    rfl
  have hh := log_loop_run rom left right (state.register .value) 0 prepared hp
    ((runOps_halted rom _ state).trans ha) (log_init_inv rom state)
  have hpheap : prepared.heap = state.heap := rfl
  have htime : 6 * Nat.clog 2 (state.register .value + 1) + 6 = 4 + (6 * Nat.clog 2 (state.register .value + 1) + 2) := by omega
  rw [htime, natRun_add, log_init_run rom left right state hpc ha]
  simpa only [Nat.zero_add, hpheap] using hh

theorem clog_succ_le (value : Nat) : Nat.clog 2 (value + 1) ≤ value := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
    by_cases hv : value = 0
    · subst value
      simp
    · have hsmall : value / 2 < value := Nat.div_lt_self (by omega) (by decide)
      have hh := ih (value / 2) hsmall
      rw [clog_half value (by omega)]
      omega

theorem log_steps_le (value : Nat) : 6 * Nat.clog 2 (value + 1) + 6 ≤ 6 * value + 6 := by
  have hh := clog_succ_le value
  omega

theorem log_dynamicTrace_le (rom : PhysicalROM) (left right : List PackingOp) (bits value : Nat)
    (state : WordState bits) :
    (packingDynamicTrace rom (left ++ logBlock left.length ++ right) (6 * Nat.clog 2 (value + 1) + 6) state).length ≤
      72 * value + 72 := by
  have hh := dynamicTrace_length_le rom (left ++ logBlock left.length ++ right) bits (6 * Nat.clog 2 (value + 1) + 6) state
  have ht := log_steps_le value
  omega

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035h
