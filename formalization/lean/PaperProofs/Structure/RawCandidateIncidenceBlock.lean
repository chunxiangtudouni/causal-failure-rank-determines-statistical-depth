module

public import PaperProofs.Structure.RawCandidateIncidenceRAM

/-! The raw candidate bit query as an active, relocated instruction block.
Only the compile-time instruction base changes; the code still reads N/q
and the incidence bits from the original raw ROM. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateIncidenceBlock

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM

def headerLead (start : Nat) : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .index 1)), .base (.base (.loadROM .input .address .index)),
   .base (.base (.constant .index (5 * (start + 31))))]

def header (start : Nat) : List PackingOp := headerLead start ++ [.jumpIfZero .old .index]

def classifyLead (start : Nat) : List PackingOp :=
  [.base (.subtract .flag .old .total), .base (.base (.constant .index (5 * (start + 21))))]

def classify (start : Nat) : List PackingOp := classifyLead start ++ [.jumpIfZero .flag .index]

def singletonLead (start : Nat) : List PackingOp :=
  [.base (.subtract .flag .old .total), .base (.base (.constant .value 1)),
   .base (.subtract .flag .flag .value), .base (.subtract .value .flag .fresh),
   .base (.subtract .flag .fresh .flag), .base (.base (.add .flag .flag .value)),
   .base (.base (.constant .value 0)), .base (.base (.constant .index (5 * (start + 31))))]

def singletonTest (start : Nat) : List PackingOp := singletonLead start ++ [.jumpIfZero .flag .index]

abbrev stageRead := RawCandidateIncidenceRAM.stageRead

def programAt (start : Nat) : List PackingOp :=
  header start ++ classify start ++ singletonTest start ++ jumpTo (start + 32) ++
    stageRead ++ jumpTo (start + 32) ++ [.base (.base (.constant .value 1))]

theorem programAt_length (start : Nat) : (programAt start).length = 32 := rfl

theorem programAt_zero : programAt 0 = RawCandidateIncidenceRAM.program := rfl

section Containing

variable (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
  (hbound : start + 32 ≤ containing.length)
  (hcode : ∀ position (hp : position < 32),
    containing[start + position]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hp start) hbound) =
      (programAt start)[position]'(Nat.lt_of_lt_of_le hp (Nat.le_of_eq (programAt_length start).symm)))

include hbound hcode

private theorem run_straight (offset : Nat) (block : List PackingOp)
    (hspan : offset + block.length ≤ 32)
    (hlocal : ∀ position (hp : position < block.length),
      (programAt start)[offset + position]'(by rw [programAt_length]; omega) = block[position])
    (hstraight : ∀ op ∈ block, NoJump op)
    (state : NatState) (hpc : state.pc = 5 * (start + offset))
    (hactive : state.halted = false) :
    natRun rom containing block.length state = runOps rom block state := by
  apply natRun_of_straight_segment rom containing block (start + offset) (by omega) ?_
    hstraight state hpc hactive
  intro position hp
  have hh := (hcode (offset + position) (by omega)).trans (hlocal position hp)
  simpa only [Nat.add_assoc] using hh

private theorem run_branch (offset : Nat) (lead : List PackingOp) (last : PackingOp)
    (hspan : offset + lead.length + 1 ≤ 32)
    (hlocal : ∀ position (hp : position < lead.length),
      (programAt start)[offset + position]'(by rw [programAt_length]; omega) = lead[position])
    (hlast : (programAt start)[offset + lead.length]'(by rw [programAt_length]; omega) = last)
    (hstraight : ∀ op ∈ lead, NoJump op)
    (state : NatState) (hpc : state.pc = 5 * (start + offset))
    (hactive : state.halted = false) :
    natRun rom containing (lead.length + 1) state = runOps rom (lead ++ [last]) state := by
  rw [runOps_append, runOps]
  apply natRun_of_segment_last rom containing lead last (start + offset) (by omega) ?_ ?_
    hstraight state hpc hactive
  · intro position hp
    have hh := (hcode (offset + position) (by omega)).trans (hlocal position hp)
    simpa only [Nat.add_assoc] using hh
  · have hh := (hcode (offset + lead.length) (by omega)).trans hlast
    simpa only [Nat.add_assoc] using hh

private theorem run_header (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    natRun rom containing 6 state = runOps rom (header start) state := by
  exact run_branch rom containing start hbound hcode 0 (headerLead start)
    (.jumpIfZero .old .index) (by simp [headerLead])
    (by intro position hp; change position < 5 at hp; interval_cases position <;> rfl)
    (by rfl) (by simp [headerLead, NoJump]) state (by simpa only [Nat.add_zero] using hpc) hactive

private theorem run_classify (state : NatState)
    (hpc : state.pc = 5 * (start + 6)) (hactive : state.halted = false) :
    natRun rom containing 3 state = runOps rom (classify start) state := by
  exact run_branch rom containing start hbound hcode 6 (classifyLead start)
    (.jumpIfZero .flag .index) (by simp [classifyLead])
    (by intro position hp; change position < 2 at hp; interval_cases position <;> rfl)
    (by rfl) (by simp [classifyLead, NoJump]) state hpc hactive

private theorem run_singleton (state : NatState)
    (hpc : state.pc = 5 * (start + 9)) (hactive : state.halted = false) :
    natRun rom containing 9 state = runOps rom (singletonTest start) state := by
  exact run_branch rom containing start hbound hcode 9 (singletonLead start)
    (.jumpIfZero .flag .index) (by simp [singletonLead])
    (by intro position hp; change position < 8 at hp; interval_cases position <;> rfl)
    (by rfl) (by simp [singletonLead, NoJump]) state hpc hactive

private theorem run_stage (state : NatState)
    (hpc : state.pc = 5 * (start + 21)) (hactive : state.halted = false) :
    natRun rom containing 7 state = runOps rom stageRead state := by
  exact run_straight rom containing start hbound hcode 21 stageRead (by decide)
    (by intro position hp; change position < 7 at hp; interval_cases position <;> rfl)
    (by simp [stageRead, RawCandidateIncidenceRAM.stageRead, NoJump]) state hpc hactive

private theorem run_exit (state : NatState) (offset : Nat) (hoffset : offset = 18 ∨ offset = 28)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing 3 state = runOps rom (jumpTo (start + 32)) state := by
  have hrun := run_branch rom containing start hbound hcode offset
    ((jumpTo (start + 32)).take 2) (.jumpIfZero .flag .index)
    (by rcases hoffset with rfl | rfl <;> change _ + 2 + 1 ≤ 32 <;> decide)
    (by
      intro position hp
      change position < 2 at hp
      rcases hoffset with rfl | rfl <;> interval_cases position <;> rfl)
    (by rcases hoffset with rfl | rfl <;> rfl)
    (by simp [jumpTo, NoJump]) state hpc hactive
  exact hrun

private theorem run_one (state : NatState)
    (hpc : state.pc = 5 * (start + 31)) (hactive : state.halted = false) :
    natRun rom containing 1 state = natExecuteOp rom (.base (.base (.constant .value 1))) state := by
  have hh := hcode 31 (by decide)
  change containing[start + 31]'(by omega) = .base (.base (.constant .value 1)) at hh
  rw [show natRun rom containing 1 state = natStep rom containing state from rfl,
    natStep_of_index rom containing state (start + 31) (by omega) hpc hactive, hh]

end Containing

def ReturnedActive (start : Nat) (before after : NatState) (answer : Nat) : Prop :=
  after.register .value = answer ∧ after.register .old = before.register .old ∧
  after.register .fresh = before.register .fresh ∧ after.heap = before.heap ∧
  after.pc = 5 * (start + 32) ∧ after.halted = false

section Query

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 32 ≤ containing.length)
  (hcode : ∀ position (hp : position < 32),
    containing[start + position]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hp start) hbound) =
      (programAt start)[position]'(Nat.lt_of_lt_of_le hp (Nat.le_of_eq (programAt_length start).symm)))

include hbound hcode

private theorem query_root (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (hroot : state.register .old = 0) :
    ReturnedActive start state (natRun (rawIncidenceROM q full) containing 7 state) 1 := by
  let rom := rawIncidenceROM q full
  have hp : (runOps rom (header start) state).pc = 5 * (start + 31) := by
    simp [header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute, hroot]
  have ha : (runOps rom (header start) state).halted = false := by rw [runOps_halted, hactive]
  rw [show 7 = 6 + 1 by decide, natRun_add,
    run_header rom containing start hbound hcode state hpc hactive,
    run_one rom containing start hbound hcode _ hp ha]
  simp [ReturnedActive, header, headerLead, runOps, natExecuteOp, Op.execute,
    Instruction.execute, hroot, hactive]
  omega

private theorem query_stage (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (hroot : state.register .old ≠ 0) (hstage : state.register .old ≤ full.length) :
    ReturnedActive start state (natRun (rawIncidenceROM q full) containing 19 state)
      ((rawIncidenceROM q full).semantic.read .input
        (2 + (state.register .old - 1) * q + state.register .fresh)) := by
  let rom := rawIncidenceROM q full
  let s₁ := runOps rom (header start) state
  let s₂ := runOps rom (classify start) s₁
  let s₃ := runOps rom stageRead s₂
  have hp₁ : s₁.pc = 5 * (start + 6) := by
    simp [s₁, header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute, hroot, hpc]
    omega
  have ha₁ : s₁.halted = false := by dsimp [s₁]; rw [runOps_halted, hactive]
  have hp₂ : s₂.pc = 5 * (start + 21) := by
    simp [s₂, s₁, classify, classifyLead, header, headerLead, runOps, natExecuteOp,
      Op.execute, Instruction.execute, rom, raw_header_N, Nat.sub_eq_zero_of_le hstage]
  have ha₂ : s₂.halted = false := by dsimp [s₂]; rw [runOps_halted, ha₁]
  have hp₃ : s₃.pc = 5 * (start + 28) := by
    rw [show s₃ = runOps rom stageRead s₂ from rfl,
      runOps_pc rom stageRead s₂ (by simp [stageRead, RawCandidateIncidenceRAM.stageRead, NoJump]), hp₂]
    change 5 * (start + 21) + 5 * 7 = 5 * (start + 28)
    omega
  have ha₃ : s₃.halted = false := by dsimp [s₃]; rw [runOps_halted, ha₂]
  have hbody : natRun rom containing 19 state = runOps rom (jumpTo (start + 32)) s₃ := by
    rw [show 19 = 6 + (3 + (7 + 3)) by decide, natRun_add,
      run_header rom containing start hbound hcode state hpc hactive]
    change natRun rom containing (3 + (7 + 3)) s₁ = _
    rw [natRun_add, run_classify rom containing start hbound hcode s₁ hp₁ ha₁]
    change natRun rom containing (7 + 3) s₂ = _
    rw [natRun_add, run_stage rom containing start hbound hcode s₂ hp₂ ha₂,
      run_exit rom containing start hbound hcode s₃ 28 (Or.inr rfl) hp₃ ha₃]
  change ReturnedActive start state (natRun rom containing 19 state) _
  rw [hbody]
  simp [ReturnedActive, s₃, s₂, s₁, stageRead, RawCandidateIncidenceRAM.stageRead,
    classify, classifyLead, header, headerLead, jumpTo, runOps, natExecuteOp,
    natArithmetic, Op.execute, Instruction.execute, rom, raw_header_N, raw_header_q,
    hactive, Nat.add_comm, Nat.add_left_comm]

private theorem query_singleton (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (hstage : full.length < state.register .old) :
    ReturnedActive start state
      (natRun (rawIncidenceROM q full) containing
        (if state.register .old - full.length - 1 = state.register .fresh then 19 else 21) state)
      (bit (decide (state.register .old - full.length - 1 = state.register .fresh))) := by
  let rom := rawIncidenceROM q full
  let s₁ := runOps rom (header start) state
  let s₂ := runOps rom (classify start) s₁
  let s₃ := runOps rom (singletonTest start) s₂
  have hroot : state.register .old ≠ 0 := by omega
  have hp₁ : s₁.pc = 5 * (start + 6) := by
    simp [s₁, header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute, hroot, hpc]
    omega
  have ha₁ : s₁.halted = false := by dsimp [s₁]; rw [runOps_halted, hactive]
  have hnotsub : state.register .old - full.length ≠ 0 := by omega
  have hp₂ : s₂.pc = 5 * (start + 9) := by
    simp [s₂, s₁, classify, classifyLead, header, headerLead, runOps, natExecuteOp,
      Op.execute, Instruction.execute, rom, raw_header_N, hnotsub, hroot, hpc]
    omega
  have ha₂ : s₂.halted = false := by dsimp [s₂]; rw [runOps_halted, ha₁]
  have ha₃ : s₃.halted = false := by dsimp [s₃]; rw [runOps_halted, ha₂]
  have hbody : natRun rom containing 18 state = s₃ := by
    rw [show 18 = 6 + (3 + 9) by decide, natRun_add,
      run_header rom containing start hbound hcode state hpc hactive]
    change natRun rom containing (3 + 9) s₁ = _
    rw [natRun_add, run_classify rom containing start hbound hcode s₁ hp₁ ha₁,
      run_singleton rom containing start hbound hcode s₂ hp₂ ha₂]
  by_cases heq : state.register .old - full.length - 1 = state.register .fresh
  · have hp₃ : s₃.pc = 5 * (start + 31) := by
      simp [s₃, s₂, s₁, singletonTest, singletonLead, classify, classifyLead, header,
        headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute, rom,
        raw_header_N, heq]
    simp only [heq, ite_true, decide_true, bit]
    rw [show 19 = 18 + 1 by decide, natRun_add, hbody,
      run_one rom containing start hbound hcode s₃ hp₃ ha₃]
    simp [ReturnedActive, s₃, s₂, s₁, singletonTest, singletonLead, classify, classifyLead,
      header, headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute,
      rom, raw_header_N, heq, hactive]
    omega
  · have hp₃ : s₃.pc = 5 * (start + 18) := by
      simp [s₃, s₂, s₁, singletonTest, singletonLead, classify, classifyLead, header,
        headerLead, runOps, natExecuteOp, Op.execute, Instruction.execute, rom,
        raw_header_N, hpc, hroot, hnotsub]
      split_ifs <;> omega
    simp only [heq, ite_false, decide_false, bit, Bool.false_eq_true]
    rw [show 21 = 18 + 3 by decide, natRun_add, hbody,
      run_exit rom containing start hbound hcode s₃ 18 (Or.inl rfl) hp₃ ha₃]
    simp [ReturnedActive, s₃, s₂, s₁, singletonTest, singletonLead, classify, classifyLead,
      header, headerLead, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute,
      rom, raw_header_N, hactive]

theorem query (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (hcandidate : state.register .old = candidate.val)
    (htool : state.register .fresh = tool.val) :
    ReturnedActive start state
      (natRun (rawIncidenceROM q full) containing
        (RawCandidateIncidenceRAM.querySteps full.length candidate.val tool.val - 1) state)
      (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
  rw [← RawCandidateIncidenceRAM.support_eq_candidateSupports_getD]
  by_cases hroot : candidate.val = 0
  · have hrun := query_root q full containing start hbound hcode state hpc hactive
      (hcandidate.trans hroot)
    simpa [RawCandidateIncidenceRAM.querySteps, RawCandidateIncidenceRAM.support, hroot, bit] using hrun
  · by_cases hstage : candidate.val ≤ full.length
    · have hrun := query_stage q full containing start hbound hcode state hpc hactive
        (by rw [hcandidate]; exact hroot) (by rw [hcandidate]; exact hstage)
      rw [hcandidate, htool, raw_bit q full ⟨candidate.val - 1, by omega⟩ tool] at hrun
      simpa [RawCandidateIncidenceRAM.querySteps, RawCandidateIncidenceRAM.support,
        hroot, hstage] using hrun
    · have hrun := query_singleton q full containing start hbound hcode state hpc hactive
        (by rw [hcandidate]; omega)
      rw [hcandidate, htool] at hrun
      by_cases heq : candidate.val - full.length - 1 = tool.val
      · simpa [RawCandidateIncidenceRAM.querySteps, RawCandidateIncidenceRAM.support,
          hroot, hstage, heq, Fin.ext_iff, eq_comm] using hrun
      · simpa [RawCandidateIncidenceRAM.querySteps, RawCandidateIncidenceRAM.support,
          hroot, hstage, heq, Ne.symm heq, Fin.ext_iff, eq_comm] using hrun

end Query

/-- In an actual append layout the body-slice hypotheses are discharged by the code itself. -/
theorem query_append (q : Nat) (full : List (Finset (Fin q)))
    (left right : List PackingOp) (candidate : Fin (full.length + q + 1)) (tool : Fin q)
    (state : NatState) (hpc : state.pc = 5 * left.length) (hactive : state.halted = false)
    (hcandidate : state.register .old = candidate.val)
    (htool : state.register .fresh = tool.val) :
    ReturnedActive left.length state
      (natRun (rawIncidenceROM q full) (left ++ programAt left.length ++ right)
        (RawCandidateIncidenceRAM.querySteps full.length candidate.val tool.val - 1) state)
      (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
  apply query q full (left ++ programAt left.length ++ right) left.length
    (by simp only [List.length_append, programAt_length]; omega) ?_
    candidate tool state hpc hactive hcandidate htool
  intro position hp
  rw [List.getElem_append_left (by simp only [List.length_append, programAt_length]; omega),
    List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

end PaperProofs.Structure.LaminarTree.RawCandidateIncidenceBlock
