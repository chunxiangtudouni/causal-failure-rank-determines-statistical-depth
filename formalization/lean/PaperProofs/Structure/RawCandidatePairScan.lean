module

public import PaperProofs.Structure.RawCandidateIncidenceBlock

/-! One fixed dynamic q-bit loop for two raw candidates.  Scratch cells are
0=q, 1/2=candidate IDs, 3=tool cursor, 4/5/6=intersection/left-only/right-only,
and 7=the temporary left bit.  No loop is unrolled according to q. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawCandidatePairScan

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open scoped BigOperators

def initBlock : List PackingOp :=
  [.base (.base (.constant .address 1)), .base (.base (.loadROM .input .total .address)),
   .base (.base (.constant .address 0)), .base (.base (.storeHeap .address .total))] ++
    setCell 3 0 ++ setCell 4 0 ++ setCell 5 0 ++ setCell 6 0

def leftArguments : List PackingOp := loadCell .old 1 ++ loadCell .fresh 3

def rightArguments : List PackingOp :=
  storeCell .value 7 ++ loadCell .old 2 ++ loadCell .fresh 3

def updateLead (start : Nat) : List PackingOp :=
  [.base (.base (.constant .flag 0)), .base (.base (.add .fresh .value .flag))] ++
    loadCell .old 7 ++ addWitness 4 (.base (.minimum .flag .old .fresh)) ++
    addWitness 5 (.subtract .flag .old .fresh) ++
    addWitness 6 (.subtract .flag .fresh .old) ++ incrementCell 3 ++ (jumpTo (start + 16)).take 2

def update (start : Nat) : List PackingOp := updateLead start ++ [.jumpIfZero .flag .index]

def programAt (start : Nat) : List PackingOp :=
  initBlock ++ testCell 0 3 (start + 125) ++ leftArguments ++
    RawCandidateIncidenceBlock.programAt (start + 27) ++ rightArguments ++
    RawCandidateIncidenceBlock.programAt (start + 65) ++ update start

theorem programAt_length (start : Nat) : (programAt start).length = 125 := rfl

def paddingOp : PackingOp := .base (.base (.constant .value 0))

theorem append_slice (left right : List PackingOp) :
    left.length + 125 ≤ (left ++ programAt left.length ++ right).length ∧
      ∀ position < 125,
        (left ++ programAt left.length ++ right).getD (left.length + position) paddingOp =
          (programAt left.length).getD position paddingOp := by
  constructor
  · simp only [List.length_append, programAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ programAt left.length) right paddingOp _ (by
      simp only [List.length_append, programAt_length]; omega),
      List.getD_append_right left (programAt left.length) paddingOp _ (by omega),
      Nat.add_sub_cancel_left]

section Containing

variable (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
  (hbound : start + 125 ≤ containing.length)
  (hcode : ∀ position < 125, containing.getD (start + position) paddingOp =
    (programAt start).getD position paddingOp)

include hbound hcode

private theorem run_straight (offset : Nat) (block : List PackingOp)
    (hspan : offset + block.length ≤ 125)
    (hlocal : ∀ position (hp : position < block.length),
      (programAt start)[offset + position]'(by rw [programAt_length]; omega) = block[position])
    (hstraight : ∀ op ∈ block, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing block.length state = runOps rom block state := by
  apply natRun_of_straight_segment rom containing block (start + offset) (by omega) ?_
    hstraight state hpc hactive
  intro position hp
  have hh := hcode (offset + position) (by omega)
  rw [List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by rw [programAt_length]; omega), hlocal position hp] at hh
  simpa only [Nat.add_assoc] using hh

private theorem run_branch (offset : Nat) (lead : List PackingOp) (last : PackingOp)
    (hspan : offset + lead.length + 1 ≤ 125)
    (hlocal : ∀ position (hp : position < lead.length),
      (programAt start)[offset + position]'(by rw [programAt_length]; omega) = lead[position])
    (hlast : (programAt start)[offset + lead.length]'(by rw [programAt_length]; omega) = last)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing (lead.length + 1) state = runOps rom (lead ++ [last]) state := by
  rw [runOps_append, runOps]
  apply natRun_of_segment_last rom containing lead last (start + offset) (by omega) ?_ ?_
    hstraight state hpc hactive
  · intro position hp
    have hh := hcode (offset + position) (by omega)
    rw [List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by rw [programAt_length]; omega), hlocal position hp] at hh
    simpa only [Nat.add_assoc] using hh
  · have hh := hcode (offset + lead.length) (by omega)
    rw [List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by rw [programAt_length]; omega), hlast] at hh
    simpa only [Nat.add_assoc] using hh

private theorem run_initBlock (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    natRun rom containing 16 state = runOps rom initBlock state := by
  exact run_straight rom containing start hbound hcode 0 initBlock (by decide)
    (by intro position hp; change position < 16 at hp; interval_cases position <;> rfl)
    (by simp [initBlock, setCell, storeCell, NoJump]) state (by simpa only [Nat.add_zero] using hpc) hactive

private theorem run_test (state : NatState)
    (hpc : state.pc = 5 * (start + 16)) (hactive : state.halted = false) :
    natRun rom containing 7 state = runOps rom (testCell 0 3 (start + 125)) state := by
  exact run_branch rom containing start hbound hcode 16
    ((testCell 0 3 (start + 125)).take 6) (.jumpIfZero .flag .index)
    (by change 16 + 6 + 1 ≤ 125; decide)
    (by intro position hp; change position < 6 at hp; interval_cases position <;> rfl)
    (by rfl) (by simp [testCell, loadCell, NoJump]) state hpc hactive

private theorem run_leftArguments (state : NatState)
    (hpc : state.pc = 5 * (start + 23)) (hactive : state.halted = false) :
    natRun rom containing 4 state = runOps rom leftArguments state := by
  exact run_straight rom containing start hbound hcode 23 leftArguments (by decide)
    (by intro position hp; change position < 4 at hp; interval_cases position <;> rfl)
    (by simp [leftArguments, loadCell, NoJump]) state hpc hactive

private theorem run_rightArguments (state : NatState)
    (hpc : state.pc = 5 * (start + 59)) (hactive : state.halted = false) :
    natRun rom containing 6 state = runOps rom rightArguments state := by
  exact run_straight rom containing start hbound hcode 59 rightArguments (by decide)
    (by intro position hp; change position < 6 at hp; interval_cases position <;> rfl)
    (by simp [rightArguments, loadCell, storeCell, NoJump]) state hpc hactive

private theorem run_update (state : NatState)
    (hpc : state.pc = 5 * (start + 97)) (hactive : state.halted = false) :
    natRun rom containing 28 state = runOps rom (update start) state := by
  exact run_branch rom containing start hbound hcode 97 (updateLead start)
    (.jumpIfZero .flag .index) (by change 97 + 27 + 1 ≤ 125; decide)
    (by intro position hp; change position < 27 at hp; interval_cases position <;> rfl)
    (by rfl) (by simp [updateLead, loadCell, addWitness, incrementCell, storeCell, jumpTo, NoJump])
    state hpc hactive

end Containing

section QueryKernels

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 125 ≤ containing.length)
  (hcode : ∀ position < 125, containing.getD (start + position) paddingOp =
    (programAt start).getD position paddingOp)

include hbound hcode

private theorem query_kernel (offset : Nat) (hoffset : offset = 27 ∨ offset = 65)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false)
    (hc : state.register .old = candidate.val) (ht : state.register .fresh = tool.val) :
    RawCandidateIncidenceBlock.ReturnedActive (start + offset) state
      (natRun (rawIncidenceROM q full) containing
        (RawCandidateIncidenceRAM.querySteps full.length candidate.val tool.val - 1) state)
      (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
  have hoff : offset ≤ 65 := by rcases hoffset with rfl | rfl <;> omega
  apply RawCandidateIncidenceBlock.query q full containing (start + offset)
    (by omega) ?_ candidate tool state hpc hactive hc ht
  intro position hp
  have hh := hcode (offset + position) (by omega)
  have hlocal : (programAt start).getD (offset + position) paddingOp =
      (RawCandidateIncidenceBlock.programAt (start + offset)).getD position paddingOp := by
    rw [List.getD_eq_getElem (programAt start) paddingOp (by rw [programAt_length]; omega),
      List.getD_eq_getElem (RawCandidateIncidenceBlock.programAt (start + offset)) paddingOp
        (by rw [RawCandidateIncidenceBlock.programAt_length]; exact hp)]
    rcases hoffset with rfl | rfl <;> interval_cases position <;> rfl
  have hout : containing.getD ((start + offset) + position) paddingOp =
      (RawCandidateIncidenceBlock.programAt (start + offset)).getD position paddingOp := by
    simpa only [Nat.add_assoc] using hh.trans hlocal
  rw [List.getD_eq_getElem containing paddingOp (by omega),
    List.getD_eq_getElem (RawCandidateIncidenceBlock.programAt (start + offset)) paddingOp
      (by rw [RawCandidateIncidenceBlock.programAt_length]; exact hp)] at hout
  exact hout

end QueryKernels

def candidateBit {q : Nat} (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) (column : Nat) : Nat :=
  if h : column < q then
    bit (decide (⟨column, h⟩ ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))
  else 0

theorem candidateBit_fin {q : Nat} (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) :
    candidateBit full candidate tool.val =
      bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅)) := by
  simp only [candidateBit, dite_eq_left tool.isLt]

def iterationSteps (N left right column : Nat) : Nat :=
  45 + (RawCandidateIncidenceRAM.querySteps N left column - 1) +
    (RawCandidateIncidenceRAM.querySteps N right column - 1)

theorem iterationSteps_le (N left right column : Nat) : iterationSteps N left right column ≤ 87 := by
  have hl := RawCandidateIncidenceRAM.querySteps_le N left column
  have hr := RawCandidateIncidenceRAM.querySteps_le N right column
  unfold iterationSteps
  omega

def Frame (before after : NatState) : Prop :=
  ∀ address, address ≠ 3 → address ≠ 4 → address ≠ 5 → address ≠ 6 → address ≠ 7 →
    after.heap address = before.heap address

private theorem runOps_update (rom : PhysicalROM) (start : Nat) (state : NatState) :
    let left := state.heap 7
    let right := state.register .value
    let result := runOps rom (update start) state
    result.heap 3 = state.heap 3 + 1 ∧
    result.heap 4 = state.heap 4 + min left right ∧
    result.heap 5 = state.heap 5 + (left - right) ∧
    result.heap 6 = state.heap 6 + (right - left) ∧
    Frame state result ∧ result.pc = 5 * (start + 16) ∧ result.halted = state.halted := by
  simp [update, updateLead, loadCell, addWitness, incrementCell, storeCell, jumpTo,
    runOps, natExecuteOp, Op.execute, Instruction.execute, Nat.add_comm, Nat.add_left_comm]
  intro address h3 h4 h5 h6 h7
  simp [h3, h4, h5, h6]

theorem iteration (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 125 ≤ containing.length)
    (hcode : ∀ position < 125, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (left right : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * (start + 16)) (hactive : state.halted = false)
    (hq : state.heap 0 = q) (hl : state.heap 1 = left.val)
    (hr : state.heap 2 = right.val) (ht : state.heap 3 = tool.val) :
    let result := natRun (rawIncidenceROM q full) containing
      (iterationSteps full.length left.val right.val tool.val) state
    result.heap 3 = state.heap 3 + 1 ∧
    result.heap 4 = state.heap 4 + min (candidateBit full left tool.val) (candidateBit full right tool.val) ∧
    result.heap 5 = state.heap 5 + (candidateBit full left tool.val - candidateBit full right tool.val) ∧
    result.heap 6 = state.heap 6 + (candidateBit full right tool.val - candidateBit full left tool.val) ∧
    Frame state result ∧ result.pc = 5 * (start + 16) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let s₀ := runOps rom (testCell 0 3 (start + 125)) state
  have htest := runOps_testCell rom 0 3 (start + 125) state
  have htestHeap : s₀.heap = state.heap := htest.1
  have htestPc : s₀.pc = 5 * (start + 23) := by
    have hp : s₀.pc = 5 * (start + 16) + 35 := by
      simpa only [s₀, hq, ht, Nat.sub_ne_zero_of_lt tool.isLt, ite_false, hpc] using htest.2.2.1
    omega
  have htestActive : s₀.halted = false := htest.2.2.2.trans hactive
  let s₁ := runOps rom leftArguments s₀
  have hp₁ : s₁.pc = 5 * (start + 27) := by
    rw [show s₁ = runOps rom leftArguments s₀ from rfl,
      runOps_pc rom leftArguments s₀ (by simp [leftArguments, loadCell, NoJump]), htestPc]
    change 5 * (start + 23) + 5 * 4 = 5 * (start + 27)
    omega
  have ha₁ : s₁.halted = false := by dsimp [s₁]; rw [runOps_halted, htestActive]
  have hh₁ : s₁.heap = state.heap := by
    simpa [s₁, leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using htestHeap
  have hl₁ : s₁.register .old = left.val := by
    simpa [s₁, leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      htestHeap] using hl
  have ht₁ : s₁.register .fresh = tool.val := by
    simpa [s₁, leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      htestHeap] using ht
  let leftSteps := RawCandidateIncidenceRAM.querySteps full.length left.val tool.val - 1
  let rightSteps := RawCandidateIncidenceRAM.querySteps full.length right.val tool.val - 1
  let s₂ := natRun rom containing leftSteps s₁
  have hleft := query_kernel q full containing start hbound hcode 27 (Or.inl rfl) left tool s₁ hp₁ ha₁ hl₁ ht₁
  rcases hleft with ⟨hv₂, _, _, hh₂, hp₂, ha₂⟩
  have hp₂ : s₂.pc = 5 * (start + 59) := by omega
  let s₃ := runOps rom rightArguments s₂
  have hp₃ : s₃.pc = 5 * (start + 65) := by
    rw [show s₃ = runOps rom rightArguments s₂ from rfl,
      runOps_pc rom rightArguments s₂ (by simp [rightArguments, loadCell, storeCell, NoJump]),
      show s₂.pc = 5 * (start + 59) from hp₂]
    change 5 * (start + 59) + 5 * 6 = 5 * (start + 65)
    omega
  have ha₃ : s₃.halted = false := by dsimp [s₃]; rw [runOps_halted, ha₂]
  have hh₃ : s₃.heap = Function.update state.heap 7 (candidateBit full left tool.val) := by
    simp [s₃, rightArguments, loadCell, storeCell, runOps, natExecuteOp, Op.execute,
      Instruction.execute, show s₂.heap = s₁.heap from hh₂, hh₁, show s₂.register .value = _ from hv₂,
      candidateBit_fin]
  have hr₃ : s₃.register .old = right.val := by
    simpa [s₃, rightArguments, loadCell, storeCell, runOps, natExecuteOp, Op.execute,
      Instruction.execute, show s₂.heap = s₁.heap from hh₂, hh₁] using hr
  have ht₃ : s₃.register .fresh = tool.val := by
    simpa [s₃, rightArguments, loadCell, storeCell, runOps, natExecuteOp, Op.execute,
      Instruction.execute, show s₂.heap = s₁.heap from hh₂, hh₁] using ht
  let s₄ := natRun rom containing rightSteps s₃
  have hright := query_kernel q full containing start hbound hcode 65 (Or.inr rfl) right tool s₃ hp₃ ha₃ hr₃ ht₃
  rcases hright with ⟨hv₄, _, _, hh₄, hp₄, ha₄⟩
  have hp₄ : s₄.pc = 5 * (start + 97) := by omega
  have hbody : natRun rom containing (iterationSteps full.length left.val right.val tool.val) state =
      runOps rom (update start) s₄ := by
    rw [show iterationSteps full.length left.val right.val tool.val =
        7 + (4 + (leftSteps + (6 + (rightSteps + 28)))) by dsimp [iterationSteps, leftSteps, rightSteps]; omega,
      natRun_add, run_test rom containing start hbound hcode state hpc hactive]
    change natRun rom containing (4 + (leftSteps + (6 + (rightSteps + 28)))) s₀ = _
    rw [natRun_add, run_leftArguments rom containing start hbound hcode s₀ htestPc htestActive]
    change natRun rom containing (leftSteps + (6 + (rightSteps + 28))) s₁ = _
    rw [natRun_add]
    change natRun rom containing (6 + (rightSteps + 28)) s₂ = _
    rw [natRun_add, run_rightArguments rom containing start hbound hcode s₂ hp₂ ha₂]
    change natRun rom containing (rightSteps + 28) s₃ = _
    rw [natRun_add]
    exact run_update rom containing start hbound hcode s₄ hp₄ ha₄
  dsimp only
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [hbody]
  have hu := runOps_update rom start s₄
  dsimp only at hu
  rw [show s₄.heap = s₃.heap from hh₄, hh₃,
    show s₄.register .value = _ from hv₄, show s₄.halted = false from ha₄,
    ← candidateBit_fin full right tool] at hu
  rcases hu with ⟨hu3, hu4, hu5, hu6, huframe, hup, hua⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hup, hua⟩
  · simpa using hu3
  · simpa using hu4
  · simpa using hu5
  · simpa using hu6
  · intro address h3 h4 h5 h6 h7
    have hf := huframe address h3 h4 h5 h6 h7
    rw [show s₄.heap = s₃.heap from hh₄, hh₃] at hf
    simpa [h7] using hf

def scanSteps (N left right count : Nat) : Nat :=
  ∑ column ∈ Finset.range count, iterationSteps N left right column

theorem scanSteps_succ (N left right count : Nat) :
    scanSteps N left right (count + 1) = scanSteps N left right count +
      iterationSteps N left right count := Finset.sum_range_succ _ _

theorem scanSteps_le (N left right count : Nat) : scanSteps N left right count ≤ 87 * count := by
  calc
    _ ≤ ∑ _column ∈ Finset.range count, 87 :=
      Finset.sum_le_sum (fun column _ => iterationSteps_le N left right column)
    _ = _ := by simp [Nat.mul_comm]

theorem scan_partial (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 125 ≤ containing.length)
    (hcode : ∀ position < 125, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * (start + 16)) (hactive : state.halted = false)
    (hq : state.heap 0 = q) (hl : state.heap 1 = left.val)
    (hr : state.heap 2 = right.val) (ht : state.heap 3 = 0)
    (count : Nat) (hcount : count ≤ q) :
    let result := natRun (rawIncidenceROM q full) containing
      (scanSteps full.length left.val right.val count) state
    result.heap 3 = count ∧
    result.heap 4 = state.heap 4 + (∑ column ∈ Finset.range count,
      min (candidateBit full left column) (candidateBit full right column)) ∧
    result.heap 5 = state.heap 5 + (∑ column ∈ Finset.range count,
      (candidateBit full left column - candidateBit full right column)) ∧
    result.heap 6 = state.heap 6 + (∑ column ∈ Finset.range count,
      (candidateBit full right column - candidateBit full left column)) ∧
    Frame state result ∧ result.pc = 5 * (start + 16) ∧ result.halted = false := by
  revert hcount
  induction count with
  | zero =>
    intro _
    simpa only [scanSteps, Finset.range_zero, Finset.sum_empty, natRun, Nat.add_zero]
      using (show state.heap 3 = 0 ∧ state.heap 4 = state.heap 4 ∧
        state.heap 5 = state.heap 5 ∧ state.heap 6 = state.heap 6 ∧ Frame state state ∧
        state.pc = 5 * (start + 16) ∧ state.halted = false from
          ⟨ht, rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl, hpc, hactive⟩)
  | succ count ih =>
    intro hcount
    rcases ih (by omega) with ⟨hk, h4, h5, h6, hframe, hp, ha⟩
    let previous := natRun (rawIncidenceROM q full) containing
      (scanSteps full.length left.val right.val count) state
    have hq' : previous.heap 0 = q :=
      (hframe 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq
    have hl' : previous.heap 1 = left.val :=
      (hframe 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
    have hr' : previous.heap 2 = right.val :=
      (hframe 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr
    have hi := iteration q full containing start hbound hcode left right ⟨count, by omega⟩
      previous hp ha hq' hl' hr' hk
    dsimp only at hi
    rcases hi with ⟨hi3, hi4, hi5, hi6, hiframe, hip, hia⟩
    have hrun : natRun (rawIncidenceROM q full) containing
        (scanSteps full.length left.val right.val (count + 1)) state =
        natRun (rawIncidenceROM q full) containing
          (iterationSteps full.length left.val right.val count) previous := by
      rw [scanSteps_succ, natRun_add]
    dsimp only
    rw [hrun]
    refine ⟨?_, ?_, ?_, ?_, ?_, hip, hia⟩
    · rw [hi3, show previous.heap 3 = count from hk]
    · rw [hi4, show previous.heap 4 = _ from h4, Finset.sum_range_succ]
      omega
    · rw [hi5, show previous.heap 5 = _ from h5, Finset.sum_range_succ]
      omega
    · rw [hi6, show previous.heap 6 = _ from h6, Finset.sum_range_succ]
      omega
    · intro address h3 h4 h5 h6 h7
      exact (hiframe address h3 h4 h5 h6 h7).trans (hframe address h3 h4 h5 h6 h7)

def totalSteps (N left right q : Nat) : Nat := 16 + scanSteps N left right q + 7

theorem totalSteps_le (N left right q : Nat) : totalSteps N left right q ≤ 87 * q + 23 := by
  have h := scanSteps_le N left right q
  unfold totalSteps
  omega

theorem totalSteps_linear (N left right q : Nat) : totalSteps N left right q ≤ 87 * (q + 1) := by
  have h := totalSteps_le N left right q
  omega

private theorem bit_sums (q : Nat) (full : List (Finset (Fin q)))
    (left right : Fin (full.length + q + 1)) :
    let L := (RawCandidateOrder.candidateSupports q full).getD left.val ∅
    let R := (RawCandidateOrder.candidateSupports q full).getD right.val ∅
    (∑ column ∈ Finset.range q, min (candidateBit full left column) (candidateBit full right column)) =
      (L ∩ R).card ∧
    (∑ column ∈ Finset.range q, (candidateBit full left column - candidateBit full right column)) =
      (L \ R).card ∧
    (∑ column ∈ Finset.range q, (candidateBit full right column - candidateBit full left column)) =
      (R \ L).card := by
  dsimp only
  constructor
  · rw [Finset.sum_range]
    convert pair_intersection_sum
      ((RawCandidateOrder.candidateSupports q full).getD left.val ∅)
      ((RawCandidateOrder.candidateSupports q full).getD right.val ∅) using 1
    apply Finset.sum_congr rfl
    intro tool _
    rw [candidateBit_fin, candidateBit_fin]
  constructor
  · rw [Finset.sum_range]
    convert pair_left_only_sum
      ((RawCandidateOrder.candidateSupports q full).getD left.val ∅)
      ((RawCandidateOrder.candidateSupports q full).getD right.val ∅) using 1
    apply Finset.sum_congr rfl
    intro tool _
    rw [candidateBit_fin, candidateBit_fin]
  · rw [Finset.sum_range]
    convert pair_right_only_sum
      ((RawCandidateOrder.candidateSupports q full).getD left.val ∅)
      ((RawCandidateOrder.candidateSupports q full).getD right.val ∅) using 1
    apply Finset.sum_congr rfl
    intro tool _
    rw [candidateBit_fin, candidateBit_fin]

/-- A complete dynamic scan returns active at its following instruction.
Candidate IDs are the only caller-provided scratch data; q and zero counters
are established by the actual initialization code. -/
theorem scan (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 125 ≤ containing.length)
    (hcode : ∀ position < 125, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val) :
    let L := (RawCandidateOrder.candidateSupports q full).getD left.val ∅
    let R := (RawCandidateOrder.candidateSupports q full).getD right.val ∅
    let result := natRun (rawIncidenceROM q full) containing
      (totalSteps full.length left.val right.val q) state
    result.heap 0 = q ∧ result.heap 3 = q ∧
    result.heap 4 = (L ∩ R).card ∧ result.heap 5 = (L \ R).card ∧ result.heap 6 = (R \ L).card ∧
    (∀ address, address ≠ 0 → address ≠ 3 → address ≠ 4 → address ≠ 5 → address ≠ 6 → address ≠ 7 →
      result.heap address = state.heap address) ∧
    result.pc = 5 * (start + 125) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom initBlock state
  have hinit : initialized.heap 0 = q ∧ initialized.heap 3 = 0 ∧ initialized.heap 4 = 0 ∧
      initialized.heap 5 = 0 ∧ initialized.heap 6 = 0 ∧
      (∀ address, address ≠ 0 → address ≠ 3 → address ≠ 4 → address ≠ 5 → address ≠ 6 →
        initialized.heap address = state.heap address) := by
    simp [initialized, initBlock, setCell, storeCell, runOps, natExecuteOp,
      Op.execute, Instruction.execute, rom, raw_header_q]
    intro address h0 h3 h4 h5 h6
    simp [h0, h3, h4, h5, h6]
  rcases hinit with ⟨hiq, hi3, hi4, hi5, hi6, hiframe⟩
  have hip : initialized.pc = 5 * (start + 16) := by
    rw [show initialized = runOps rom initBlock state from rfl,
      runOps_pc rom initBlock state (by simp [initBlock, setCell, storeCell, NoJump]), hpc]
    change 5 * start + 5 * 16 = 5 * (start + 16)
    omega
  have hia : initialized.halted = false := by dsimp [initialized]; rw [runOps_halted, hactive]
  have hil : initialized.heap 1 = left.val :=
    (hiframe 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
  have hir : initialized.heap 2 = right.val :=
    (hiframe 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr
  have hs := scan_partial q full containing start hbound hcode left right initialized
    hip hia hiq hil hir hi3 q le_rfl
  dsimp only at hs
  rcases bit_sums q full left right with ⟨hsum4, hsum5, hsum6⟩
  rw [hi4, hi5, hi6, Nat.zero_add, hsum4, hsum5, hsum6] at hs
  simp only [Nat.zero_add] at hs
  rcases hs with ⟨hs3, hs4, hs5, hs6, hsframe, hsp, hsa⟩
  let previous := natRun rom containing (scanSteps full.length left.val right.val q) initialized
  have hpreviousq : previous.heap 0 = q :=
    (hsframe 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hiq
  have hexit := runOps_testCell rom 0 3 (start + 125) previous
  have hrun : natRun rom containing (totalSteps full.length left.val right.val q) state =
      runOps rom (testCell 0 3 (start + 125)) previous := by
    rw [show totalSteps full.length left.val right.val q =
        16 + (scanSteps full.length left.val right.val q + 7) by unfold totalSteps; omega,
      natRun_add, run_initBlock rom containing start hbound hcode state hpc hactive]
    change natRun rom containing (scanSteps full.length left.val right.val q + 7) initialized = _
    rw [natRun_add]
    exact run_test rom containing start hbound hcode previous hsp hsa
  dsimp only
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [hrun]
  refine ⟨(congrFun hexit.1 0).trans hpreviousq, (congrFun hexit.1 3).trans hs3,
    (congrFun hexit.1 4).trans hs4, (congrFun hexit.1 5).trans hs5,
    (congrFun hexit.1 6).trans hs6, ?_, ?_, hexit.2.2.2.trans hsa⟩
  · intro address h0 h3 h4 h5 h6 h7
    exact (congrFun hexit.1 address).trans
      ((hsframe address h3 h4 h5 h6 h7).trans (hiframe address h0 h3 h4 h5 h6))
  · simpa only [hpreviousq, show previous.heap 3 = q from hs3, Nat.sub_self, ite_true]
      using hexit.2.2.1

end PaperProofs.Structure.LaminarTree.RawCandidatePairScan
