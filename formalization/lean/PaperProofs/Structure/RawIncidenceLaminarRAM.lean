module

public import PaperProofs.Structure.RawTreePreprocessingClaims
public import PaperProofs.Structure.PackingMachine
import Mathlib.Tactic.IntervalCases

/-! A fixed raw-incidence laminarity checker. The code receives only the
original [N,q] header and N*q incidence bits. The three pair counters count
intersection, left-only, and right-only witnesses. Neither a set comparison
nor a precomputed result/trace is an instruction or an input word.

This phase does not construct the serialized inclusion tree and is not the
whole RawTreePreprocessingClaims.FullClaims theorem. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
open PackingMachine

/-- Eight fixed scratch cells: N,q,i,j,k,intersection,left-only,right-only. -/
def loadCell (target : Register) (cell : Nat) : List PackingOp :=
  [.base (.base (.constant .address cell)), .base (.base (.loadHeap target .address))]

def storeCell (source : Register) (cell : Nat) : List PackingOp :=
  [.base (.base (.constant .address cell)), .base (.base (.storeHeap .address source))]

def setCell (cell value : Nat) : List PackingOp :=
  [.base (.base (.constant .total value))] ++ storeCell .total cell

def incrementCell (cell : Nat) : List PackingOp :=
  loadCell .old cell ++ [.base (.base (.constant .total 1)), .base (.base (.add .old .old .total))] ++
    storeCell .old cell

/-- Targets are encoded word addresses, not instruction indexes. -/
def jumpTo (index : Nat) : List PackingOp :=
  [.base (.base (.constant .flag 0)), .base (.base (.constant .index (5 * index))),
    .jumpIfZero .flag .index]

def testCell (bound counter exit : Nat) : List PackingOp :=
  loadCell .total bound ++ loadCell .old counter ++
    [.base (.subtract .flag .total .old), .base (.base (.constant .index (5 * exit))),
      .jumpIfZero .flag .index]

def readPairBit (row : Nat) (target : Register) : List PackingOp :=
  loadCell .index row ++ loadCell .total 1 ++
    [.arithmetic .multiply .index .index .total] ++ loadCell .total 4 ++
    [.base (.base (.add .index .index .total)), .base (.base (.constant .total 2)),
      .base (.base (.add .index .index .total)), .base (.base (.loadROM .input target .index))]

def addWitness (cell : Nat) (operation : Op) : List PackingOp :=
  [.base (.base (.constant .address cell)), .base (.base (.loadHeap .total .address)),
    .base operation, .base (.base (.add .total .total .flag)),
    .base (.base (.storeHeap .address .total))]

/-- A fixed 37-op kernel. Its outputs are actual three RAM counters. -/
def pairBitKernel : List PackingOp :=
  readPairBit 2 .old ++ readPairBit 3 .fresh ++
    addWitness 5 (.base (.minimum .flag .old .fresh)) ++
    addWitness 6 (.subtract .flag .old .fresh) ++
    addWitness 7 (.subtract .flag .fresh .old)

def pairBitLoopBody : List PackingOp :=
  pairBitKernel ++ incrementCell 4 ++ jumpTo 39

def pairBitStraight : List PackingOp :=
  pairBitKernel ++ incrementCell 4 ++ (jumpTo 39).take 2

def pairCounterTest (cell : Nat) : List PackingOp :=
  loadCell .total cell ++ [.base (.base (.constant .index (5 * 108))), .jumpIfZero .total .index]

def checker : List PackingOp :=
  [.base (.base (.constant .address 0)), .base (.base (.loadROM .input .total .address)),
    .base (.base (.storeHeap .address .total)),
    .base (.base (.constant .address 1)), .base (.base (.loadROM .input .total .address)),
    .base (.base (.storeHeap .address .total)), .base (.base (.constant .value 1))] ++
  setCell 2 0 ++
  testCell 0 2 126 ++ setCell 3 0 ++
  testCell 0 3 117 ++ setCell 4 0 ++ setCell 5 0 ++ setCell 6 0 ++ setCell 7 0 ++
  testCell 1 4 92 ++ pairBitLoopBody ++
  pairCounterTest 5 ++ pairCounterTest 6 ++ pairCounterTest 7 ++
  [.base (.base (.constant .value 0))] ++ jumpTo 126 ++
  incrementCell 3 ++ jumpTo 20 ++ incrementCell 2 ++ jumpTo 10

theorem checker_length : checker.length = 126 := rfl
theorem pairBitKernel_length : pairBitKernel.length = 37 := rfl
theorem pairBitLoopBody_length : pairBitLoopBody.length = 46 := rfl
theorem pairBitStraight_length : pairBitStraight.length = 45 := rfl
theorem pairBitLoopBody_split : pairBitLoopBody = pairBitStraight ++ [.jumpIfZero .flag .index] := rfl
theorem checker_pairBitKernel : (checker.drop 46).take 37 = pairBitKernel := rfl
theorem checker_outer : checker[10]? = some (.base (.base (.constant .address 0))) := rfl
theorem checker_pair : checker[20]? = some (.base (.base (.constant .address 0))) := rfl
theorem checker_bit : checker[39]? = some (.base (.base (.constant .address 1))) := rfl
theorem checker_pair_done : checker[92]? = some (.base (.base (.constant .address 5))) := rfl
theorem checker_next_pair : checker[108]? = some (.base (.base (.constant .address 3))) := rfl
theorem checker_next_row : checker[117]? = some (.base (.base (.constant .address 2))) := rfl

theorem incidence_length (q : Nat) (full : List (Finset (Fin q))) :
    (incidence full).length = full.length * q := by
  induction full with
  | nil => simp [incidence]
  | cons eligible later ih =>
    simp only [incidence, List.flatMap_cons, List.length_append, List.length_map,
      List.length_finRange, List.length_cons] at *
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem incidence_getD (q : Nat) (full : List (Finset (Fin q)))
    (row : Nat) (hrow : row < full.length) (tool : Fin q) :
    (incidence full).getD (row * q + tool.val) 0 =
      bit (decide (tool ∈ full[row])) := by
  induction full generalizing row with
  | nil => simp only [List.length_nil] at hrow; omega
  | cons eligible later ih =>
    cases row with
    | zero =>
      simp only [incidence, List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_map, List.length_finRange] using tool.isLt)]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_finRange] using tool.isLt)]
      simp
    | succ row =>
      have hr : row < later.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hrow
      simp only [incidence, List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by
        simp only [List.length_map, List.length_finRange, Nat.add_mul, Nat.one_mul]
        omega)]
      have haddress : (row + 1) * q + tool.val -
          ((List.finRange q).map (fun tool => bit (decide (tool ∈ eligible)))).length = row * q + tool.val := by
        simp only [List.length_map, List.length_finRange, Nat.add_mul, Nat.one_mul]
        omega
      rw [haddress]
      exact ih row hr

theorem raw_input_length (q : Nat) (full : List (Finset (Fin q))) :
    ((rawIncidenceROM q full).words .input).length = 2 + full.length * q := by
  simp only [rawIncidenceROM, PhysicalROM.words, List.length_append, List.length_cons,
    List.length_nil, incidence_length]

theorem raw_header_N (q : Nat) (full : List (Finset (Fin q))) :
    (rawIncidenceROM q full).semantic.read .input 0 = full.length := rfl

theorem raw_header_q (q : Nat) (full : List (Finset (Fin q))) :
    (rawIncidenceROM q full).semantic.read .input 1 = q := rfl

theorem raw_bit (q : Nat) (full : List (Finset (Fin q)))
    (row : Fin full.length) (tool : Fin q) :
    (rawIncidenceROM q full).semantic.read .input (2 + row.val * q + tool.val) =
      bit (decide (tool ∈ full[row.val])) := by
  change ([full.length, q] ++ incidence full).getD (2 + row.val * q + tool.val) 0 = _
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
  have haddress : 2 + row.val * q + tool.val - [full.length, q].length = row.val * q + tool.val := by
    simp only [List.length_cons, List.length_nil]
    omega
  rw [haddress]
  exact incidence_getD q full row.val row.isLt tool

/-- A proof composition of the original instructions on the original
natural view of RAM state. This is not an instruction or a machine input. -/
def runOps (rom : PhysicalROM) : List PackingOp → NatState → NatState
  | [], state => state
  | op :: rest, state => runOps rom rest (natExecuteOp rom op state)

def NoJump : PackingOp → Prop
  | .jumpIfZero _ _ => False
  | _ => True

theorem natExecuteOp_pc_noJump (rom : PhysicalROM) (op : PackingOp) (state : NatState)
    (h : NoJump op) : (natExecuteOp rom op state).pc = state.pc + 5 := by
  cases op with
  | base op =>
    cases op with
    | base instruction => cases instruction <;> rfl
    | subtract target left right => rfl
  | arithmetic operation target left right => rfl
  | jumpIfZero condition target => exact h.elim

theorem natExecuteOp_halted (rom : PhysicalROM) (op : PackingOp) (state : NatState) :
    (natExecuteOp rom op state).halted = state.halted := by
  cases op with
  | base op =>
    cases op with
    | base instruction => cases instruction <;> rfl
    | subtract target left right => rfl
  | arithmetic operation target left right => rfl
  | jumpIfZero condition target => rfl

theorem runOps_append (rom : PhysicalROM) (left right : List PackingOp) (state : NatState) :
    runOps rom (left ++ right) state = runOps rom right (runOps rom left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons op rest ih => exact ih _

theorem runOps_halted (rom : PhysicalROM) (block : List PackingOp) (state : NatState) :
    (runOps rom block state).halted = state.halted := by
  induction block generalizing state with
  | nil => rfl
  | cons op rest ih => rw [runOps, ih, natExecuteOp_halted]

theorem runOps_pc (rom : PhysicalROM) (block : List PackingOp) (state : NatState)
    (hstraight : ∀ op ∈ block, NoJump op) :
    (runOps rom block state).pc = state.pc + 5 * block.length := by
  induction block generalizing state with
  | nil => simp [runOps]
  | cons op rest ih =>
    rw [runOps, ih _ (fun other hm => hstraight other (List.mem_cons_of_mem _ hm)),
      natExecuteOp_pc_noJump rom op state (hstraight op List.mem_cons_self), List.length_cons]
    omega

theorem natRun_of_straight_segment (rom : PhysicalROM) (program block : List PackingOp)
    (start : Nat) (hbound : start + block.length ≤ program.length)
    (hcode : ∀ position (hposition : position < block.length),
      program[start + position]'(by omega) = block[position])
    (hstraight : ∀ op ∈ block, NoJump op)
    (state : NatState) (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    natRun rom program block.length state = runOps rom block state := by
  induction block generalizing start state with
  | nil => rfl
  | cons op later ih =>
    have hindex : start < program.length := by
      simp only [List.length_cons] at hbound
      omega
    have hhead := hcode 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hhead
    change natRun rom program later.length (natStep rom program state) =
      runOps rom later (natExecuteOp rom op state)
    rw [natStep_of_index rom program state start hindex hpc hactive, hhead]
    refine ih (start + 1) (by simp only [List.length_cons] at hbound; omega) ?_
      (fun other hm => hstraight other (List.mem_cons_of_mem _ hm))
      (natExecuteOp rom op state) ?_ ?_
    · intro position hposition
      have hh := hcode (position + 1) (by simpa using hposition)
      change program[start + (position + 1)]'(by simp only [List.length_cons] at hbound; omega) =
        later[position] at hh
      convert hh using 1
      congr 1
      omega
    · rw [natExecuteOp_pc_noJump rom op state (hstraight op List.mem_cons_self), hpc]
      omega
    · rw [natExecuteOp_halted, hactive]

theorem natRun_of_segment_last (rom : PhysicalROM) (program lead : List PackingOp)
    (last : PackingOp) (start : Nat) (hbound : start + lead.length + 1 ≤ program.length)
    (hcode : ∀ position (hposition : position < lead.length),
      program[start + position]'(by omega) = lead[position])
    (hlast : program[start + lead.length]'(by omega) = last)
    (hstraight : ∀ op ∈ lead, NoJump op)
    (state : NatState) (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    natRun rom program (lead.length + 1) state = natExecuteOp rom last (runOps rom lead state) := by
  rw [natRun_succ,
    natRun_of_straight_segment rom program lead start (by omega) hcode hstraight state hpc hactive,
    natStep_of_index rom program (runOps rom lead state) (start + lead.length) (by omega)
      (by rw [runOps_pc rom lead state hstraight, hpc]; omega)
      (by rw [runOps_halted, hactive]), hlast]

theorem checker_kernel_code (position : Nat) (hposition : position < pairBitKernel.length) :
    checker[46 + position]'(by rw [checker_length]; rw [pairBitKernel_length] at hposition; omega) =
      pairBitKernel[position] := by
  rw [pairBitKernel_length] at hposition
  interval_cases position <;> rfl

theorem pairBitKernel_noJump : ∀ op ∈ pairBitKernel, NoJump op := by
  simp [pairBitKernel, readPairBit, loadCell, addWitness, NoJump]

/-- The fixed kernel is executed by actual encoded fetch/decode, at its
actual location in the single dimension-independent checker. -/
theorem natRun_checker_pairBitKernel (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 230) (hactive : state.halted = false) :
    natRun rom checker 37 state = runOps rom pairBitKernel state := by
  exact natRun_of_straight_segment rom checker pairBitKernel 46
    (by rw [pairBitKernel_length, checker_length]; omega) checker_kernel_code
    pairBitKernel_noJump state hpc hactive

theorem natRun_checker_pairBitLoopBody (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 230) (hactive : state.halted = false) :
    natRun rom checker 46 state = runOps rom pairBitLoopBody state := by
  have hcode : ∀ position (hposition : position < pairBitStraight.length),
      checker[46 + position]'(by rw [checker_length]; rw [pairBitStraight_length] at hposition; omega) =
        pairBitStraight[position] := by
    intro position hposition
    rw [pairBitStraight_length] at hposition
    interval_cases position <;> rfl
  have hstraight : ∀ op ∈ pairBitStraight, NoJump op := by
    simp [pairBitStraight, pairBitKernel, readPairBit, loadCell, addWitness, incrementCell,
      storeCell, jumpTo, NoJump]
  have hrun := natRun_of_segment_last rom checker pairBitStraight (.jumpIfZero .flag .index) 46
    (by rw [pairBitStraight_length, checker_length]; omega) hcode (by rfl) hstraight state hpc hactive
  simpa only [pairBitStraight_length, pairBitLoopBody_split, runOps_append, runOps] using hrun

theorem natRun_checker_bitTest (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 195) (hactive : state.halted = false) :
    natRun rom checker 7 state = runOps rom (testCell 1 4 92) state := by
  let lead := (testCell 1 4 92).take 6
  have hlength : lead.length = 6 := rfl
  have hcode : ∀ position (hposition : position < lead.length),
      checker[39 + position]'(by rw [checker_length]; rw [hlength] at hposition; omega) =
        lead[position] := by
    intro position hposition
    rw [hlength] at hposition
    interval_cases position <;> rfl
  have hstraight : ∀ op ∈ lead, NoJump op := by
    simp [lead, testCell, loadCell, NoJump]
  have hrun := natRun_of_segment_last rom checker lead (.jumpIfZero .flag .index) 39
    (by rw [hlength, checker_length]; omega) hcode (by rfl) hstraight state hpc hactive
  exact hrun

theorem runOps_testCell (rom : PhysicalROM) (bound counter exit : Nat) (state : NatState) :
    let result := runOps rom (testCell bound counter exit) state
    result.heap = state.heap ∧ result.register .value = state.register .value ∧
      result.pc = (if state.heap bound - state.heap counter = 0 then 5 * exit else state.pc + 35) ∧
      result.halted = state.halted := by
  simp [runOps, testCell, loadCell, natExecuteOp, Op.execute, Instruction.execute,
    Nat.add_assoc]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem runOps_pairBitLoopBody (rom : PhysicalROM) (state : NatState) :
    let left := rom.semantic.read .input (2 + state.heap 2 * state.heap 1 + state.heap 4)
    let right := rom.semantic.read .input (2 + state.heap 3 * state.heap 1 + state.heap 4)
    let result := runOps rom pairBitLoopBody state
    result.heap 4 = state.heap 4 + 1 ∧
    result.heap 5 = state.heap 5 + min left right ∧
    result.heap 6 = state.heap 6 + (left - right) ∧
    result.heap 7 = state.heap 7 + (right - left) ∧
    (∀ address, address ≠ 4 → address ≠ 5 → address ≠ 6 → address ≠ 7 → result.heap address = state.heap address) ∧
    result.register .value = state.register .value ∧ result.pc = 195 ∧
    result.halted = state.halted := by
  simp [runOps, pairBitLoopBody, pairBitKernel, readPairBit, loadCell, addWitness, incrementCell,
    storeCell, jumpTo, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  intro address h4 h5 h6 h7
  simp [h4, h5, h6, h7]

/-- One genuine q-loop iteration: seven fetched test instructions and
forty-six fetched body instructions, ending at the original loop address. -/
theorem natRun_checker_pairIteration (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 195) (hactive : state.halted = false)
    (hlive : state.heap 4 < state.heap 1) :
    let left := rom.semantic.read .input (2 + state.heap 2 * state.heap 1 + state.heap 4)
    let right := rom.semantic.read .input (2 + state.heap 3 * state.heap 1 + state.heap 4)
    let result := natRun rom checker 53 state
    result.heap 4 = state.heap 4 + 1 ∧
    result.heap 5 = state.heap 5 + min left right ∧
    result.heap 6 = state.heap 6 + (left - right) ∧
    result.heap 7 = state.heap 7 + (right - left) ∧
    (∀ address, address ≠ 4 → address ≠ 5 → address ≠ 6 → address ≠ 7 → result.heap address = state.heap address) ∧
    result.register .value = state.register .value ∧ result.pc = 195 ∧ result.halted = false := by
  let tested := runOps rom (testCell 1 4 92) state
  have ht := runOps_testCell rom 1 4 92 state
  have htestedPc : tested.pc = 230 := by
    simpa only [tested, Nat.sub_ne_zero_of_lt hlive, ite_false, hpc] using ht.2.2.1
  have htestedActive : tested.halted = false := ht.2.2.2.trans hactive
  have hrun : natRun rom checker 53 state = runOps rom pairBitLoopBody tested := by
    rw [show 53 = 7 + 46 from rfl, natRun_add, natRun_checker_bitTest rom state hpc hactive]
    exact natRun_checker_pairBitLoopBody rom tested htestedPc htestedActive
  rw [hrun]
  have hb := runOps_pairBitLoopBody rom tested
  dsimp only at hb
  rw [show tested.heap = state.heap from ht.1,
    show tested.register .value = state.register .value from ht.2.1, htestedActive] at hb
  exact hb

def leftAt (rom : PhysicalROM) (state : NatState) (offset : Nat) : Nat :=
  rom.semantic.read .input (2 + state.heap 2 * state.heap 1 + state.heap 4 + offset)

def rightAt (rom : PhysicalROM) (state : NatState) (offset : Nat) : Nat :=
  rom.semantic.read .input (2 + state.heap 3 * state.heap 1 + state.heap 4 + offset)

open scoped BigOperators

/-- A whole arbitrary prefix of the q-bit scan is a real encoded run. The
sum is a proof specification; no sum or set operation is a RAM instruction. -/
theorem natRun_checker_pairScan_partial (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 195) (hactive : state.halted = false)
    (count : Nat) (hwithin : state.heap 4 + count ≤ state.heap 1) :
    let result := natRun rom checker (53 * count) state
    result.heap 4 = state.heap 4 + count ∧
    result.heap 5 = state.heap 5 + (∑ offset ∈ Finset.range count, min (leftAt rom state offset) (rightAt rom state offset)) ∧
    result.heap 6 = state.heap 6 + (∑ offset ∈ Finset.range count, (leftAt rom state offset - rightAt rom state offset)) ∧
    result.heap 7 = state.heap 7 + (∑ offset ∈ Finset.range count, (rightAt rom state offset - leftAt rom state offset)) ∧
    (∀ address, address ≠ 4 → address ≠ 5 → address ≠ 6 → address ≠ 7 → result.heap address = state.heap address) ∧
    result.register .value = state.register .value ∧ result.pc = 195 ∧ result.halted = false := by
  revert hwithin
  induction count with
  | zero =>
    intro _
    simpa only [Nat.mul_zero, natRun, Finset.range_zero, Finset.sum_empty, Nat.add_zero,
      hpc, hactive] using (show
      state.heap 4 = state.heap 4 ∧ state.heap 5 = state.heap 5 ∧ state.heap 6 = state.heap 6 ∧
      state.heap 7 = state.heap 7 ∧
      (∀ address, address ≠ 4 → address ≠ 5 → address ≠ 6 → address ≠ 7 → state.heap address = state.heap address) ∧
      state.register .value = state.register .value ∧ 195 = 195 ∧ false = false from
      ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩)
  | succ count ih =>
    intro hwithin
    rcases ih (by omega) with ⟨hk, h5, h6, h7, hframe, hv, hp, hh⟩
    let previous := natRun rom checker (53 * count) state
    have hq : previous.heap 1 = state.heap 1 := hframe 1 (by decide) (by decide) (by decide) (by decide)
    have hi : previous.heap 2 = state.heap 2 := hframe 2 (by decide) (by decide) (by decide) (by decide)
    have hj : previous.heap 3 = state.heap 3 := hframe 3 (by decide) (by decide) (by decide) (by decide)
    have hnext : previous.heap 4 < previous.heap 1 := by
      rw [show previous.heap 4 = state.heap 4 + count from hk, hq]
      omega
    have hs := natRun_checker_pairIteration rom previous hp hh hnext
    dsimp only at hs
    have hleft : rom.semantic.read .input (2 + previous.heap 2 * previous.heap 1 + previous.heap 4) =
        leftAt rom state count := by
      rw [hi, hq, show previous.heap 4 = state.heap 4 + count from hk]
      simp only [leftAt, Nat.add_assoc]
    have hright : rom.semantic.read .input (2 + previous.heap 3 * previous.heap 1 + previous.heap 4) =
        rightAt rom state count := by
      rw [hj, hq, show previous.heap 4 = state.heap 4 + count from hk]
      simp only [rightAt, Nat.add_assoc]
    rw [hleft, hright] at hs
    rcases hs with ⟨hsk, hs5, hs6, hs7, hsframe, hsv, hsp, hsh⟩
    have hrun : natRun rom checker (53 * (count + 1)) state = natRun rom checker 53 previous := by
      rw [Nat.mul_succ, natRun_add]
    dsimp only
    rw [hrun]
    refine ⟨?_, ?_, ?_, ?_, ?_, hsv.trans hv, hsp, hsh⟩
    · rw [hsk, show previous.heap 4 = state.heap 4 + count from hk]
      omega
    · rw [hs5, show previous.heap 5 = _ from h5, Finset.sum_range_succ]
      omega
    · rw [hs6, show previous.heap 6 = _ from h6, Finset.sum_range_succ]
      omega
    · rw [hs7, show previous.heap 7 = _ from h7, Finset.sum_range_succ]
      omega
    · intro address h4 h5 h6 h7
      exact (hsframe address h4 h5 h6 h7).trans (hframe address h4 h5 h6 h7)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem runOps_pairBitKernel (rom : PhysicalROM) (state : NatState) :
    let left := rom.semantic.read .input (2 + state.heap 2 * state.heap 1 + state.heap 4)
    let right := rom.semantic.read .input (2 + state.heap 3 * state.heap 1 + state.heap 4)
    let result := runOps rom pairBitKernel state
    result.heap 5 = state.heap 5 + min left right ∧
    result.heap 6 = state.heap 6 + (left - right) ∧
    result.heap 7 = state.heap 7 + (right - left) ∧
    (∀ address, address ≠ 5 → address ≠ 6 → address ≠ 7 → result.heap address = state.heap address) ∧
    result.register .value = state.register .value ∧ result.pc = state.pc + 185 ∧
    result.halted = state.halted := by
  simp [runOps, pairBitKernel, readPairBit, loadCell, addWitness, natExecuteOp,
    natArithmetic, Op.execute, Instruction.execute, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  intro address h5 h6 h7
  simp [h5, h6, h7]

theorem natRun_checker_pairBitKernel_raw (q : Nat) (full : List (Finset (Fin q)))
    (left right : Fin full.length) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 230) (hactive : state.halted = false)
    (hq : state.heap 1 = q) (hleft : state.heap 2 = left.val)
    (hright : state.heap 3 = right.val) (htool : state.heap 4 = tool.val) :
    let result := natRun (rawIncidenceROM q full) checker 37 state
    result.heap 5 = state.heap 5 + (if tool ∈ full[left.val] ∩ full[right.val] then 1 else 0) ∧
    result.heap 6 = state.heap 6 + (if tool ∈ full[left.val] \ full[right.val] then 1 else 0) ∧
    result.heap 7 = state.heap 7 + (if tool ∈ full[right.val] \ full[left.val] then 1 else 0) ∧
    (∀ address, address ≠ 5 → address ≠ 6 → address ≠ 7 → result.heap address = state.heap address) ∧
    result.register .value = state.register .value ∧ result.pc = 415 ∧ result.halted = false := by
  rw [natRun_checker_pairBitKernel _ state hpc hactive]
  have hkernel := runOps_pairBitKernel (rawIncidenceROM q full) state
  dsimp only at hkernel
  rw [hq, hleft, hright, htool, raw_bit, raw_bit, hpc, hactive] at hkernel
  by_cases hl : tool ∈ full[left.val] <;> by_cases hr : tool ∈ full[right.val] <;>
    simpa [bit, hl, hr] using hkernel

open scoped BigOperators

theorem pair_intersection_sum {q : Nat} (left right : Finset (Fin q)) :
    (∑ tool : Fin q, min (bit (decide (tool ∈ left))) (bit (decide (tool ∈ right)))) =
      (left ∩ right).card := by
  calc
    _ = ∑ tool : Fin q, if tool ∈ left ∩ right then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro tool _
      by_cases hl : tool ∈ left <;> by_cases hr : tool ∈ right <;> simp [bit, hl, hr]
    _ = _ := by
      simp
      congr 1
      ext tool
      simp

theorem pair_left_only_sum {q : Nat} (left right : Finset (Fin q)) :
    (∑ tool : Fin q, (bit (decide (tool ∈ left)) - bit (decide (tool ∈ right)))) =
      (left \ right).card := by
  calc
    _ = ∑ tool : Fin q, if tool ∈ left \ right then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro tool _
      by_cases hl : tool ∈ left <;> by_cases hr : tool ∈ right <;> simp [bit, hl, hr]
    _ = _ := by
      simp
      congr 1
      ext tool
      simp

theorem pair_right_only_sum {q : Nat} (left right : Finset (Fin q)) :
    (∑ tool : Fin q, (bit (decide (tool ∈ right)) - bit (decide (tool ∈ left)))) =
      (right \ left).card := pair_left_only_sum right left

theorem pair_laminar_iff_counter_zero {q : Nat} (left right : Finset (Fin q)) :
    Disjoint left right ∨ left ⊆ right ∨ right ⊆ left ↔
      (left ∩ right).card = 0 ∨ (left \ right).card = 0 ∨ (right \ left).card = 0 := by
  simp only [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset,
    Finset.disjoint_iff_inter_eq_empty]

theorem laminarSchedule_iff_all_pair_counters_zero (q : Nat) (full : List (Finset (Fin q))) :
    LaminarSchedule full ↔ ∀ left : Fin full.length, ∀ right : Fin full.length,
      (full[left.val] ∩ full[right.val]).card = 0 ∨
        (full[left.val] \ full[right.val]).card = 0 ∨
          (full[right.val] \ full[left.val]).card = 0 := by
  constructor
  · intro h left right
    exact (pair_laminar_iff_counter_zero _ _).mp
      (h _ (List.getElem_mem left.isLt) _ (List.getElem_mem right.isLt))
  · intro h left hleft right hright
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hleft
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hright
    exact (pair_laminar_iff_counter_zero _ _).mpr (h ⟨i, hi⟩ ⟨j, hj⟩)

/-- The complete q-bit pair scan, including its final encoded exit test,
returns the three exact set-witness counts. The entry hypotheses are only
concrete scratch-cell contents and the actual code location. -/
theorem natRun_checker_pairScan_raw (q : Nat) (full : List (Finset (Fin q)))
    (left right : Fin full.length) (state : NatState)
    (hpc : state.pc = 195) (hactive : state.halted = false)
    (hq : state.heap 1 = q) (hleft : state.heap 2 = left.val)
    (hright : state.heap 3 = right.val) (hk : state.heap 4 = 0)
    (h5 : state.heap 5 = 0) (h6 : state.heap 6 = 0) (h7 : state.heap 7 = 0) :
    let result := natRun (rawIncidenceROM q full) checker (53 * q + 7) state
    result.heap 4 = q ∧ result.heap 5 = (full[left.val] ∩ full[right.val]).card ∧
    result.heap 6 = (full[left.val] \ full[right.val]).card ∧
    result.heap 7 = (full[right.val] \ full[left.val]).card ∧
    (∀ address, address ≠ 4 → address ≠ 5 → address ≠ 6 → address ≠ 7 → result.heap address = state.heap address) ∧
    result.register .value = state.register .value ∧ result.pc = 460 ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  have hleftBit (tool : Fin q) : leftAt rom state tool.val = bit (decide (tool ∈ full[left.val])) := by
    simpa only [leftAt, hleft, hq, hk, Nat.add_zero] using raw_bit q full left tool
  have hrightBit (tool : Fin q) : rightAt rom state tool.val = bit (decide (tool ∈ full[right.val])) := by
    simpa only [rightAt, hright, hq, hk, Nat.add_zero] using raw_bit q full right tool
  have hinter : (∑ offset ∈ Finset.range q, min (leftAt rom state offset) (rightAt rom state offset)) =
      (full[left.val] ∩ full[right.val]).card := by
    rw [Finset.sum_range]
    convert pair_intersection_sum full[left.val] full[right.val] using 1
    apply Finset.sum_congr rfl
    intro tool _
    rw [hleftBit, hrightBit]
  have hleftOnly : (∑ offset ∈ Finset.range q, (leftAt rom state offset - rightAt rom state offset)) =
      (full[left.val] \ full[right.val]).card := by
    rw [Finset.sum_range]
    convert pair_left_only_sum full[left.val] full[right.val] using 1
    apply Finset.sum_congr rfl
    intro tool _
    rw [hleftBit, hrightBit]
  have hrightOnly : (∑ offset ∈ Finset.range q, (rightAt rom state offset - leftAt rom state offset)) =
      (full[right.val] \ full[left.val]).card := by
    rw [Finset.sum_range]
    convert pair_right_only_sum full[left.val] full[right.val] using 1
    apply Finset.sum_congr rfl
    intro tool _
    rw [hleftBit, hrightBit]
  have hp := natRun_checker_pairScan_partial rom state hpc hactive q (by rw [hk, hq]; omega)
  dsimp only at hp
  rw [hk, h5, h6, h7, Nat.zero_add, hinter, hleftOnly, hrightOnly] at hp
  simp only [Nat.zero_add] at hp
  rcases hp with ⟨hpk, hp5, hp6, hp7, hpframe, hpv, hpp, hph⟩
  let previous := natRun rom checker (53 * q) state
  have ht := runOps_testCell rom 1 4 92 previous
  have hrun : natRun rom checker (53 * q + 7) state = runOps rom (testCell 1 4 92) previous := by
    rw [natRun_add]
    exact natRun_checker_bitTest rom previous hpp hph
  dsimp only
  rw [hrun]
  refine ⟨(congrFun ht.1 4).trans hpk, (congrFun ht.1 5).trans hp5,
    (congrFun ht.1 6).trans hp6, (congrFun ht.1 7).trans hp7, ?_, ht.2.1.trans hpv, ?_, ht.2.2.2.trans hph⟩
  · intro address h4 h5 h6 h7
    exact (congrFun ht.1 address).trans (hpframe address h4 h5 h6 h7)
  · have hpreviousq : previous.heap 1 = q :=
      (hpframe 1 (by decide) (by decide) (by decide) (by decide)).trans hq
    rw [ht.2.2.1, hpreviousq, show previous.heap 4 = q from hpk]
    simp

end PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM
