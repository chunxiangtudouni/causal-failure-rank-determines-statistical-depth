module

public import PaperProofs.Structure.RawIncidenceLaminarRAM
public import PaperProofs.Structure.RawCandidateOrder

/-! A fixed raw-input bit query for the unfiltered candidates: root, every
original stage (including empty stages), then singleton tools in tool order.
The caller supplies only two legal indexes in `.old` and `.fresh`; the code
reads N and q itself.  This component is not the complete tree constructor. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateIncidenceRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM

def candidates (q : Nat) (full : List (Finset (Fin q))) : List (Finset (Fin q)) :=
  Finset.univ :: (full ++ List.ofFn (fun tool : Fin q => ({tool} : Finset (Fin q))))

theorem candidates_length (q : Nat) (full : List (Finset (Fin q))) :
    (candidates q full).length = full.length + q + 1 := by
  simp only [candidates, List.length_cons, List.length_append, List.length_ofFn]

def support (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) : Finset (Fin q) :=
  if hroot : candidate.val = 0 then Finset.univ
  else if hstage : candidate.val ≤ full.length then
    full[candidate.val - 1]'(by omega)
  else {⟨candidate.val - full.length - 1, by have hc := candidate.isLt; omega⟩}

theorem support_eq_candidate (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) :
    support q full candidate = (candidates q full)[candidate.val]'(by
      rw [candidates_length]; exact candidate.isLt) := by
  unfold support
  split_ifs with hroot hstage
  · simp only [candidates, hroot, List.getElem_cons_zero]
  · have hpositive : 0 < candidate.val := by omega
    simp only [candidates, List.getElem_cons, hroot, dite_false]
    rw [List.getElem_append_left (by omega)]
  · have hpositive : 0 < candidate.val := by omega
    simp only [candidates, List.getElem_cons, hroot, dite_false]
    rw [List.getElem_append_right (by omega)]
    simp only [List.getElem_ofFn]
    congr 1
    apply Fin.ext
    change candidate.val - full.length - 1 = candidate.val - 1 - full.length
    omega

theorem support_eq_candidateSupports_getD (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) :
    support q full candidate =
      (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅ := by
  have hi : candidate.val < (RawCandidateOrder.candidateSupports q full).length := by
    rw [RawCandidateOrder.candidateSupports_length]
    exact candidate.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact support_eq_candidate q full candidate

def headerLead : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .index 1)), .base (.base (.loadROM .input .address .index)),
   .base (.base (.constant .index 155))]

def header : List PackingOp := headerLead ++ [.jumpIfZero .old .index]

def classifyLead : List PackingOp :=
  [.base (.subtract .flag .old .total), .base (.base (.constant .index 105))]

def classify : List PackingOp := classifyLead ++ [.jumpIfZero .flag .index]

def singletonLead : List PackingOp :=
  [.base (.subtract .flag .old .total), .base (.base (.constant .value 1)),
   .base (.subtract .flag .flag .value), .base (.subtract .value .flag .fresh),
   .base (.subtract .flag .fresh .flag), .base (.base (.add .flag .flag .value)),
   .base (.base (.constant .value 0)), .base (.base (.constant .index 155))]

def singletonTest : List PackingOp := singletonLead ++ [.jumpIfZero .flag .index]

def stageRead : List PackingOp :=
  [.base (.base (.constant .value 1)), .base (.subtract .flag .old .value),
   .arithmetic .multiply .flag .flag .address, .base (.base (.add .flag .flag .fresh)),
   .base (.base (.constant .index 2)), .base (.base (.add .index .flag .index)),
   .base (.base (.loadROM .input .value .index))]

def program : List PackingOp :=
  header ++ classify ++ singletonTest ++ jumpTo 32 ++ stageRead ++ jumpTo 32 ++
    [.base (.base (.constant .value 1))]

theorem program_length : program.length = 32 := rfl

private theorem run_header (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false) :
    natRun rom program 6 state = runOps rom header state := by
  have hrun := natRun_of_segment_last rom program headerLead (.jumpIfZero .old .index) 0
    (by decide) (by intro position hp; change position < 5 at hp; interval_cases position <;> rfl)
    (by rfl) (by simp [headerLead, NoJump]) state hpc hactive
  change natRun rom program 6 state = _ at hrun
  simpa only [header, runOps_append, runOps] using hrun

private theorem run_classify (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 30) (hactive : state.halted = false) :
    natRun rom program 3 state = runOps rom classify state := by
  have hrun := natRun_of_segment_last rom program classifyLead (.jumpIfZero .flag .index) 6
    (by decide) (by intro position hp; change position < 2 at hp; interval_cases position <;> rfl)
    (by rfl) (by simp [classifyLead, NoJump]) state hpc hactive
  change natRun rom program 3 state = _ at hrun
  simpa only [classify, runOps_append, runOps] using hrun

private theorem run_singleton (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 45) (hactive : state.halted = false) :
    natRun rom program 9 state = runOps rom singletonTest state := by
  have hrun := natRun_of_segment_last rom program singletonLead (.jumpIfZero .flag .index) 9
    (by decide) (by intro position hp; change position < 8 at hp; interval_cases position <;> rfl)
    (by rfl) (by simp [singletonLead, NoJump]) state hpc hactive
  change natRun rom program 9 state = _ at hrun
  simpa only [singletonTest, runOps_append, runOps] using hrun

private theorem run_stage (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 105) (hactive : state.halted = false) :
    natRun rom program 7 state = runOps rom stageRead state := by
  exact natRun_of_straight_segment rom program stageRead 21 (by decide)
    (by intro position hp; change position < 7 at hp; interval_cases position <;> rfl)
    (by simp [stageRead, NoJump]) state hpc hactive

private theorem run_exit (rom : PhysicalROM) (state : NatState)
    (start : Nat) (hstart : start = 18 ∨ start = 28)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    natRun rom program 3 state = runOps rom (jumpTo 32) state := by
  have hs : start ≤ 28 := by rcases hstart with rfl | rfl <;> omega
  have hb : start + ((jumpTo 32).take 2).length + 1 ≤ program.length := by
    rcases hstart with rfl | rfl <;> decide
  have hc : ∀ position (hp : position < ((jumpTo 32).take 2).length),
      program[start + position]'(by change position < 2 at hp; change start + position < 32; omega) =
        ((jumpTo 32).take 2)[position] := by
    intro position hp
    change position < 2 at hp
    rcases hstart with rfl | rfl <;> interval_cases position <;> rfl
  have hl : program[start + ((jumpTo 32).take 2).length]'(by
      rcases hstart with rfl | rfl <;> decide) = .jumpIfZero .flag .index := by
    rcases hstart with rfl | rfl <;> rfl
  have hrun := natRun_of_segment_last rom program ((jumpTo 32).take 2)
    (.jumpIfZero .flag .index) start hb hc hl
    (by simp [jumpTo, NoJump]) state hpc hactive
  exact hrun

private theorem run_one (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 155) (hactive : state.halted = false) :
    natRun rom program 1 state = natExecuteOp rom (.base (.base (.constant .value 1))) state := by
  exact natStep_of_index rom program state 31 (by decide) hpc hactive

private theorem run_halt (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 160) (hactive : state.halted = false) :
    natRun rom program 1 state = { state with halted := true } := by
  exact natStep_halt rom program state hpc hactive

def querySteps (N candidate tool : Nat) : Nat :=
  if candidate = 0 then 8 else if candidate ≤ N then 20
  else if candidate - N - 1 = tool then 20 else 22

def Returned (before after : NatState) (answer : Nat) : Prop :=
  after.register .value = answer ∧ after.register .old = before.register .old ∧
  after.register .fresh = before.register .fresh ∧ after.heap = before.heap ∧
  after.pc = 160 ∧ after.halted = true

private theorem finish_return (rom : PhysicalROM) (before state : NatState) (answer : Nat)
    (hpc : state.pc = 160) (hactive : state.halted = false)
    (hvalue : state.register .value = answer)
    (hold : state.register .old = before.register .old)
    (hfresh : state.register .fresh = before.register .fresh) (hheap : state.heap = before.heap) :
    Returned before (natRun rom program 1 state) answer := by
  rw [run_halt rom state hpc hactive]
  exact ⟨hvalue, hold, hfresh, hheap, hpc, rfl⟩

theorem query_root (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hroot : state.register .old = 0) :
    Returned state (natRun (rawIncidenceROM q full) program 8 state) 1 ∧
      (natRun (rawIncidenceROM q full) program 7 state).halted = false := by
  let rom := rawIncidenceROM q full
  have hp : (runOps rom header state).pc = 155 := by
    simp [header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute, hroot]
  have ha : (runOps rom header state).halted = false := by rw [runOps_halted, hactive]
  have hbody : natRun rom program 7 state =
      natExecuteOp rom (.base (.base (.constant .value 1))) (runOps rom header state) := by
    rw [show 7 = 6 + 1 by decide, natRun_add, run_header rom state hpc hactive,
      run_one rom _ hp ha]
  constructor
  · change Returned state (natRun rom program 8 state) 1
    rw [show 8 = 7 + 1 by decide, natRun_add, hbody]
    apply finish_return
    all_goals simp [header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute,
      hroot, hactive]
  · change (natRun rom program 7 state).halted = false
    rw [hbody, natExecuteOp_halted, runOps_halted, hactive]

theorem query_stage (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hroot : state.register .old ≠ 0) (hstage : state.register .old ≤ full.length) :
    Returned state (natRun (rawIncidenceROM q full) program 20 state)
      ((rawIncidenceROM q full).semantic.read .input
        (2 + (state.register .old - 1) * q + state.register .fresh)) ∧
      (natRun (rawIncidenceROM q full) program 19 state).halted = false := by
  let rom := rawIncidenceROM q full
  let s₁ := runOps rom header state
  let s₂ := runOps rom classify s₁
  let s₃ := runOps rom stageRead s₂
  have hp₁ : s₁.pc = 30 := by
    simp [s₁, header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute, hroot, hpc]
  have ha₁ : s₁.halted = false := by dsimp [s₁]; rw [runOps_halted, hactive]
  have hp₂ : s₂.pc = 105 := by
    simp [s₂, s₁, classify, classifyLead, header, headerLead, runOps, natExecuteOp,
      Op.execute, Instruction.execute, rom, raw_header_N, Nat.sub_eq_zero_of_le hstage]
  have ha₂ : s₂.halted = false := by dsimp [s₂]; rw [runOps_halted, ha₁]
  have hp₃ : s₃.pc = 140 := by
    rw [show s₃ = runOps rom stageRead s₂ from rfl,
      runOps_pc rom stageRead s₂ (by simp [stageRead, NoJump]), hp₂]
    rfl
  have ha₃ : s₃.halted = false := by dsimp [s₃]; rw [runOps_halted, ha₂]
  have hbody : natRun rom program 19 state = runOps rom (jumpTo 32) s₃ := by
    rw [show 19 = 6 + (3 + (7 + 3)) by decide, natRun_add,
      run_header rom state hpc hactive]
    change natRun rom program (3 + (7 + 3)) s₁ = _
    rw [natRun_add, run_classify rom s₁ hp₁ ha₁]
    change natRun rom program (7 + 3) s₂ = _
    rw [natRun_add, run_stage rom s₂ hp₂ ha₂, run_exit rom s₃ 28 (Or.inr rfl) hp₃ ha₃]
  constructor
  · change Returned state (natRun rom program 20 state) _
    rw [show 20 = 19 + 1 by decide, natRun_add, hbody]
    apply finish_return
    all_goals simp [s₃, s₂, s₁, stageRead, classify, classifyLead, header, headerLead,
      jumpTo, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      rom, raw_header_N, raw_header_q, hactive, Nat.add_comm, Nat.add_left_comm]
  · change (natRun rom program 19 state).halted = false
    rw [hbody, runOps_halted, ha₃]

theorem query_singleton (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hstage : full.length < state.register .old) :
    Returned state
      (natRun (rawIncidenceROM q full) program
        (if state.register .old - full.length - 1 = state.register .fresh then 20 else 22) state)
      (bit (decide (state.register .old - full.length - 1 = state.register .fresh))) ∧
      (natRun (rawIncidenceROM q full) program
        (if state.register .old - full.length - 1 = state.register .fresh then 19 else 21) state).halted = false := by
  let rom := rawIncidenceROM q full
  let s₁ := runOps rom header state
  let s₂ := runOps rom classify s₁
  let s₃ := runOps rom singletonTest s₂
  have hroot : state.register .old ≠ 0 := by omega
  have hp₁ : s₁.pc = 30 := by
    simp [s₁, header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute, hroot, hpc]
  have ha₁ : s₁.halted = false := by dsimp [s₁]; rw [runOps_halted, hactive]
  have hnotsub : state.register .old - full.length ≠ 0 := by omega
  have hp₂ : s₂.pc = 45 := by
    simp [s₂, s₁, classify, classifyLead, header, headerLead, runOps, natExecuteOp,
      Op.execute, Instruction.execute, rom, raw_header_N, hnotsub, hroot, hpc]
  have ha₂ : s₂.halted = false := by dsimp [s₂]; rw [runOps_halted, ha₁]
  have ha₃ : s₃.halted = false := by dsimp [s₃]; rw [runOps_halted, ha₂]
  have hbody : natRun rom program 18 state = s₃ := by
    rw [show 18 = 6 + (3 + 9) by decide, natRun_add, run_header rom state hpc hactive]
    change natRun rom program (3 + 9) s₁ = _
    rw [natRun_add, run_classify rom s₁ hp₁ ha₁, run_singleton rom s₂ hp₂ ha₂]
  by_cases heq : state.register .old - full.length - 1 = state.register .fresh
  · have hp₃ : s₃.pc = 155 := by
      simp [s₃, s₂, s₁, singletonTest, singletonLead, classify, classifyLead, header,
        headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute, rom,
        raw_header_N, heq]
    simp only [heq, ite_true, decide_true, bit]
    constructor
    · rw [show 20 = 18 + (1 + 1) by decide, natRun_add, hbody, natRun_add,
        run_one rom s₃ hp₃ ha₃]
      apply finish_return
      all_goals simp [s₃, s₂, s₁, singletonTest, singletonLead, classify, classifyLead,
        header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute,
        rom, raw_header_N, heq, hactive]
    · rw [show 19 = 18 + 1 by decide, natRun_add, hbody, run_one rom s₃ hp₃ ha₃,
        natExecuteOp_halted, ha₃]
  · have hsum :
        (state.register .fresh - (state.register .old - full.length - 1)) +
          (state.register .old - full.length - 1 - state.register .fresh) ≠ 0 := by omega
    have hp₃ : s₃.pc = 90 := by
      simp [s₃, s₂, s₁, singletonTest, singletonLead, classify, classifyLead, header,
        headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute, rom,
        raw_header_N, hpc, hroot, hnotsub]
      omega
    simp only [heq, ite_false, decide_false, bit, Bool.false_eq_true]
    constructor
    · rw [show 22 = 18 + (3 + 1) by decide, natRun_add, hbody, natRun_add,
        run_exit rom s₃ 18 (Or.inl rfl) hp₃ ha₃]
      apply finish_return
      all_goals simp [s₃, s₂, s₁, singletonTest, singletonLead, classify, classifyLead,
        header, headerLead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute,
        rom, raw_header_N, hactive]
    · rw [show 21 = 18 + 3 by decide, natRun_add, hbody,
        run_exit rom s₃ 18 (Or.inl rfl) hp₃ ha₃, runOps_halted, ha₃]

theorem query (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hcandidate : state.register .old = candidate.val)
    (htool : state.register .fresh = tool.val) :
    Returned state
      (natRun (rawIncidenceROM q full) program (querySteps full.length candidate.val tool.val) state)
      (bit (decide (tool ∈ support q full candidate))) := by
  by_cases hroot : candidate.val = 0
  · have hrun := query_root q full state hpc hactive (hcandidate.trans hroot)
    simpa [querySteps, support, hroot, bit] using hrun.1
  · by_cases hstage : candidate.val ≤ full.length
    · have hrun := query_stage q full state hpc hactive
        (by rw [hcandidate]; exact hroot) (by rw [hcandidate]; exact hstage)
      rw [hcandidate, htool, raw_bit q full ⟨candidate.val - 1, by omega⟩ tool] at hrun
      simpa [querySteps, support, hroot, hstage] using hrun.1
    · have hrun := query_singleton q full state hpc hactive (by rw [hcandidate]; omega)
      rw [hcandidate, htool] at hrun
      simpa [querySteps, support, hroot, hstage, Fin.ext_iff, eq_comm] using hrun.1

theorem querySteps_pos (N candidate tool : Nat) : 0 < querySteps N candidate tool := by
  unfold querySteps
  split_ifs <;> decide

theorem querySteps_le (N candidate tool : Nat) : querySteps N candidate tool ≤ 22 := by
  unfold querySteps
  split_ifs <;> decide

private theorem natRun_halted_fixed (rom : PhysicalROM) (count : Nat) (state : NatState)
    (hhalted : state.halted = true) : natRun rom program count state = state := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [natRun, natStep, hhalted, ite_true] using ih

private theorem active_prefix_of_endpoint (rom : PhysicalROM) (state : NatState)
    (endpoint : Nat) (hactive : (natRun rom program endpoint state).halted = false)
    (clock : Nat) (hclock : clock ≤ endpoint) :
    (natRun rom program clock state).halted = false := by
  cases hh : (natRun rom program clock state).halted with
  | false => rfl
  | true =>
    have hsame : natRun rom program endpoint state = natRun rom program clock state := by
      conv_lhs => rw [show endpoint = clock + (endpoint - clock) by omega]
      rw [natRun_add, natRun_halted_fixed rom _ _ hh]
    rw [hsame, hh] at hactive
    cases hactive

theorem query_before_halt (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hcandidate : state.register .old = candidate.val)
    (htool : state.register .fresh = tool.val) :
    (natRun (rawIncidenceROM q full) program
      (querySteps full.length candidate.val tool.val - 1) state).halted = false := by
  by_cases hroot : candidate.val = 0
  · simpa [querySteps, hroot] using
      (query_root q full state hpc hactive (hcandidate.trans hroot)).2
  · by_cases hstage : candidate.val ≤ full.length
    · simpa [querySteps, hroot, hstage] using
        (query_stage q full state hpc hactive (by rw [hcandidate]; exact hroot)
          (by rw [hcandidate]; exact hstage)).2
    · have hrun := (query_singleton q full state hpc hactive (by rw [hcandidate]; omega)).2
      rw [hcandidate, htool] at hrun
      by_cases heq : candidate.val - full.length - 1 = tool.val
      · simpa [querySteps, hroot, hstage, heq] using hrun
      · simpa [querySteps, hroot, hstage, heq] using hrun

/-- The stated clock is the first HALT clock, not merely an eventual upper bound. -/
theorem query_active_prefix (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hcandidate : state.register .old = candidate.val)
    (htool : state.register .fresh = tool.val) :
    ∀ clock < querySteps full.length candidate.val tool.val,
      (natRun (rawIncidenceROM q full) program clock state).halted = false := by
  intro clock hclock
  exact active_prefix_of_endpoint _ state _
    (query_before_halt q full candidate tool state hpc hactive hcandidate htool) clock (by omega)

theorem query_candidateSupports (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hcandidate : state.register .old = candidate.val)
    (htool : state.register .fresh = tool.val) :
    Returned state
      (natRun (rawIncidenceROM q full) program (querySteps full.length candidate.val tool.val) state)
      (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
  rw [← support_eq_candidateSupports_getD]
  exact query q full candidate tool state hpc hactive hcandidate htool

theorem query_value_le_one (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 0) (hactive : state.halted = false)
    (hcandidate : state.register .old = candidate.val)
    (htool : state.register .fresh = tool.val) :
    (natRun (rawIncidenceROM q full) program (querySteps full.length candidate.val tool.val) state).register .value ≤ 1 := by
  rw [(query q full candidate tool state hpc hactive hcandidate htool).1]
  unfold bit
  split_ifs <;> decide

end PaperProofs.Structure.LaminarTree.RawCandidateIncidenceRAM
