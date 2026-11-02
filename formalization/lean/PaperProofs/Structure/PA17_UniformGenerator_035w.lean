module

public import PaperProofs.Structure.PA17_UniformGenerator_035u

/-! Whole real logarithm-loop prefix safety. Registers are bounded from
the runtime halving/count invariant; clog is only the proved clock measure. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035w

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035h PA17UniformGenerator035i PA17UniformGenerator035j
  PA17UniformGenerator035l PA17UniformGenerator035m PA17UniformGenerator035u

theorem logHead_safe (rom : PhysicalROM) (B heapWords exitIndex : Nat) (left right : List PackingOp)
    (hexit : 5 * exitIndex ≤ B) (ht : exitIndex ≤ (left ++ logHead (5 * exitIndex) ++ right).length)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state) :
    RunSafe B heapWords rom (left ++ logHead (5 * exitIndex) ++ right) 2 state := by
  let lead : List PackingOp := [.base (.base (.constant .old (5 * exitIndex)))]
  have hcode : logHead (5 * exitIndex) = lead ++ [.jumpIfZero .value .old] := rfl
  rw [hcode]
  apply branch_segment_safe rom B heapWords left lead right (.jumpIfZero .value .old)
    (by simp [lead, NoJump]) state hpc ha (by rw [← hcode]; exact logHead_numeric rom B heapWords _ hexit state hr)
  rw [← hcode]
  by_cases hz : state.register .value = 0
  · exact ⟨exitIndex, ht, by rw [log_head_pc, ite_eq_left hz]⟩
  · refine ⟨left.length + 2, by simp only [List.length_append]; change left.length + 2 ≤ left.length + 2 + right.length; omega, ?_⟩
    rw [log_head_pc, ite_eq_right hz, hpc]
    omega

theorem logTail_safe (rom : PhysicalROM) (B heapWords entryIndex : Nat) (left right : List PackingOp)
    (he : 5 * entryIndex ≤ B) (ht : entryIndex ≤ (left ++ logTail (5 * entryIndex) ++ right).length)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hz : state.register .flag = 0) (hadd : state.register .index + state.register .total ≤ B) :
    RunSafe B heapWords rom (left ++ logTail (5 * entryIndex) ++ right) 4 state := by
  let lead := (logTail (5 * entryIndex)).take 3
  have hcode : logTail (5 * entryIndex) = lead ++ [.jumpIfZero .flag .old] := rfl
  rw [hcode]
  apply branch_segment_safe rom B heapWords left lead right (.jumpIfZero .flag .old)
    (by simp [lead, logTail, NoJump]) state hpc ha (by rw [← hcode]; exact logTail_numeric rom B heapWords _ he state hr hadd)
  rw [← hcode]
  exact ⟨entryIndex, ht, log_tail_pc rom _ state hz⟩

theorem log_loop_safe (rom : PhysicalROM) (B heapWords : Nat) (left right : List PackingOp)
    (hpcB : 5 * (left ++ logBlock left.length ++ right).length ≤ B)
    (value offset : Nat) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 4)) (ha : state.halted = false) (hr : RegistersLE B state)
    (hi : LogInv offset value state) (hindex : offset + Nat.clog 2 (value + 1) ≤ B) :
    RunSafe B heapWords rom (left ++ logBlock left.length ++ right)
      (6 * Nat.clog 2 (value + 1) + 2) state := by
  induction value using Nat.strong_induction_on generalizing offset state with
  | h value ih =>
    let allCode := left ++ logBlock left.length ++ right
    have hshead : RunSafe B heapWords rom allCode 2 state := by
      have hp : (left ++ logInit).length = left.length + 4 := by simp [logInit]
      have hh := logHead_safe rom B heapWords (left.length + 10) (left ++ logInit) (logTail (5 * (left.length + 4)) ++ right)
        (by simp only [List.length_append, logBlock_length] at hpcB; omega)
        (by
          have hh : (logHead (5 * (left.length + 10))).length = 2 := rfl
          have ht : (logTail (5 * (left.length + 4))).length = 4 := rfl
          simp only [List.length_append, hp, hh, ht]
          omega)
        state (by rw [hp]; exact hpc) ha hr
      simpa only [allCode, logBlock, hp, List.append_assoc] using hh
    have hheadRun : natRun rom allCode 2 state = runOps rom (logHead (5 * (left.length + 10))) state :=
      log_head_run rom left right state hpc ha
    by_cases hv : value = 0
    · subst value
      simpa only [Nat.zero_add, Nat.clog_one_right, Nat.mul_zero] using hshead
    · let tested := runOps rom (logHead (5 * (left.length + 10))) state
      have ht := log_head_inv rom (5 * (left.length + 10)) offset value state hi
      have htpc : tested.pc = 5 * (left.length + 6) := by
        rw [log_head_pc, hi.2.1, ite_eq_right hv, hpc]
        omega
      have hta : tested.halted = false := (runOps_halted rom _ state).trans ha
      have htreg : RegistersLE B tested := by
        have hh := (hshead.final _ _ _ _ _).1
        rw [hheadRun] at hh
        exact hh
      have hindex1 : offset + 1 ≤ B := by
        rw [clog_half value (by omega)] at hindex
        omega
      have hstail : RunSafe B heapWords rom allCode 4 tested := by
        let lead := left ++ logInit ++ logHead (5 * (left.length + 10))
        have hp : lead.length = left.length + 6 := by simp [lead, logInit, logHead]
        have hh := logTail_safe rom B heapWords (left.length + 4) lead right
          (by simp only [List.length_append, logBlock_length] at hpcB; omega)
          (by simp only [List.length_append, hp]; change left.length + 4 ≤ left.length + 6 + 4 + right.length; omega)
          tested (by rw [hp]; exact htpc) hta htreg ht.2.2.2.2
          (by rw [ht.1, ht.2.2.2.1]; exact hindex1)
        simpa only [allCode, logBlock, lead, List.append_assoc] using hh
      let divided := runOps rom (logTail (5 * (left.length + 4))) tested
      have htailRun : natRun rom allCode 4 tested = divided := log_tail_run rom left right tested htpc hta
      have hd := log_tail_inv rom (5 * (left.length + 4)) offset value tested ht
      have hdpc : divided.pc = 5 * (left.length + 4) := log_tail_pc rom _ tested ht.2.2.2.2
      have hda : divided.halted = false := (runOps_halted rom _ tested).trans hta
      have hdreg : RegistersLE B divided := by
        have hh := (hstail.final _ _ _ _ _).1
        rw [htailRun] at hh
        exact hh
      have hsmall : value / 2 < value := Nat.div_lt_self (by omega) (by decide)
      have hremaining := ih (value / 2) hsmall (offset + 1) divided hdpc hda hdreg hd
        (by rw [clog_half value (by omega)] at hindex; omega)
      have hcycleRun : natRun rom allCode (2 + 4) state = divided := by rw [natRun_add, hheadRun, htailRun]
      have hsfirst := RunSafe.add _ _ _ allCode 2 4 state hshead (by rw [hheadRun]; exact hstail)
      have hsall := RunSafe.add B heapWords rom allCode (2 + 4) (6 * Nat.clog 2 (value / 2 + 1) + 2) state hsfirst
        (by rw [hcycleRun]; exact hremaining)
      have htime : 6 * Nat.clog 2 (value + 1) + 2 = (2 + 4) + (6 * Nat.clog 2 (value / 2 + 1) + 2) := by
        rw [clog_half value (by omega)]
        omega
      rw [htime]
      exact hsall

theorem log_safe (rom : PhysicalROM) (B heapWords : Nat) (left right : List PackingOp)
    (hpcB : 5 * (left ++ logBlock left.length ++ right).length ≤ B) (htwo : 2 ≤ B)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state) :
    RunSafe B heapWords rom (left ++ logBlock left.length ++ right)
      (6 * Nat.clog 2 (state.register .value + 1) + 6) state := by
  let allCode := left ++ logBlock left.length ++ right
  let prepared := runOps rom logInit state
  have hinitSafe : RunSafe B heapWords rom allCode 4 state := by
    have hlen : logInit.length = 4 := rfl
    have hh := straight_segment_safe rom B heapWords left logInit
      (logHead (5 * (left.length + 10)) ++ logTail (5 * (left.length + 4)) ++ right)
      (by simp [logInit, NoJump]) state hpc ha (logInit_numeric rom B heapWords htwo state hr)
    simpa only [allCode, logBlock, List.append_assoc, hlen] using hh
  have hinitRun : natRun rom allCode 4 state = prepared := log_init_run rom left right state hpc ha
  have hp : prepared.pc = 5 * (left.length + 4) := by
    rw [runOps_pc rom logInit state (by simp [logInit, NoJump]), hpc]
    rfl
  have hreg : RegistersLE B prepared := by
    have hh := (hinitSafe.final _ _ _ _ _).1
    rw [hinitRun] at hh
    exact hh
  have hlater := log_loop_safe rom B heapWords left right hpcB (state.register .value) 0 prepared hp
    ((runOps_halted rom logInit state).trans ha) hreg (log_init_inv rom state)
    (by simpa only [Nat.zero_add] using (clog_succ_le (state.register .value)).trans (hr .value))
  have htime : 6 * Nat.clog 2 (state.register .value + 1) + 6 = 4 + (6 * Nat.clog 2 (state.register .value + 1) + 2) := by omega
  rw [htime]
  exact RunSafe.add _ _ _ _ _ _ state hinitSafe (by rw [hinitRun]; exact hlater)

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035w
