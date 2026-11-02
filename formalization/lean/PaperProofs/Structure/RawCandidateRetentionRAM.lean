module

public import PaperProofs.Structure.RawCandidatePairScan
public import PaperProofs.Structure.RawCandidateRetentionFlags
import Mathlib.Tactic.Linarith

/-! Fixed-code runtime candidate retention.  The workspace pointer is read
from heap[8], and its header stores M=N+q+1.  No cardinality or retention
answer is provided to the program. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateRetentionRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open scoped BigOperators

def loadWorkspace (target : Register) (offset : Nat) : List PackingOp :=
  loadCell .address 8 ++ [.base (.base (.constant .index offset)),
    .base (.base (.add .address .address .index)), .base (.base (.loadHeap target .address))]

def storeWorkspace (offset : Nat) : List PackingOp :=
  loadCell .address 8 ++ [.base (.base (.constant .index offset)),
    .base (.base (.add .address .address .index)), .base (.base (.storeHeap .address .total))]

def setWorkspace (offset value : Nat) : List PackingOp :=
  [.base (.base (.constant .total value))] ++ storeWorkspace offset

def incrementWorkspace (offset : Nat) : List PackingOp :=
  loadWorkspace .total offset ++ [.base (.base (.constant .old 1)),
    .base (.base (.add .total .total .old))] ++ storeWorkspace offset

def testWorkspace (counter exit : Nat) : List PackingOp :=
  loadWorkspace .total 0 ++ loadWorkspace .old counter ++
    [.base (.subtract .flag .total .old), .base (.base (.constant .index (5 * exit))),
      .jumpIfZero .flag .index]

def cardArguments : List PackingOp :=
  loadWorkspace .old 1 ++ storeCell .old 1 ++ setCell 2 0

def pairArguments : List PackingOp :=
  loadWorkspace .old 1 ++ storeCell .old 1 ++ loadWorkspace .old 2 ++ storeCell .old 2

def storeCard : List PackingOp :=
  loadCell .total 4 ++ loadCell .old 1 ++ loadCell .address 8 ++
    [.base (.base (.constant .index 4)), .base (.base (.add .address .address .index)),
     .base (.base (.add .address .address .old)), .base (.base (.storeHeap .address .total))]

def setInitialFlag : List PackingOp :=
  [.base (.base (.constant .old 1)), .base (.base (.minimum .total .old .total))] ++ storeWorkspace 3

def initializeLater : List PackingOp :=
  loadCell .total 1 ++ [.base (.base (.constant .old 1)), .base (.base (.add .total .total .old))] ++
    storeWorkspace 2

def afterCard : List PackingOp := storeCard ++ setInitialFlag ++ initializeLater

def updateFlag : List PackingOp :=
  loadCell .total 5 ++ loadCell .old 6 ++ [.base (.base (.add .flag .total .old))] ++
    loadWorkspace .total 3 ++ [.base (.base (.constant .old 0)),
      .base (.base (.select .total .flag .total .old))] ++ storeWorkspace 3

def innerTail (start : Nat) : List PackingOp :=
  updateFlag ++ incrementWorkspace 2 ++ jumpTo (start + 180)

def storeKeep : List PackingOp :=
  loadWorkspace .total 3 ++ loadCell .old 1 ++ loadWorkspace .fresh 0 ++ loadCell .address 8 ++
    [.base (.base (.constant .index 4)), .base (.base (.add .address .address .index)),
     .base (.base (.add .address .address .fresh)), .base (.base (.add .address .address .old)),
     .base (.base (.storeHeap .address .total))]

def finishCandidate (start : Nat) : List PackingOp :=
  storeKeep ++ incrementWorkspace 1 ++ jumpTo (start + 6)

def beforeCard (start : Nat) : List PackingOp :=
  setWorkspace 1 0 ++ testWorkspace 1 (start + 398) ++ cardArguments

def betweenScans (start : Nat) : List PackingOp :=
  afterCard ++ testWorkspace 2 (start + 364) ++ pairArguments

def programAt (start : Nat) : List PackingOp :=
  beforeCard start ++ RawCandidatePairScan.programAt (start + 29) ++ betweenScans start ++
    RawCandidatePairScan.programAt (start + 207) ++ innerTail start ++ finishCandidate start

theorem beforeCard_length (start : Nat) : (beforeCard start).length = 29 := by
  simp only [beforeCard, setWorkspace, storeWorkspace, testWorkspace, loadWorkspace,
    cardArguments, loadCell, storeCell, setCell, List.length_append, List.length_cons, List.length_nil]

theorem betweenScans_length (start : Nat) : (betweenScans start).length = 53 := by
  simp only [betweenScans, afterCard, storeCard, setInitialFlag, initializeLater,
    testWorkspace, loadWorkspace, storeWorkspace, pairArguments, loadCell, storeCell,
    List.length_append, List.length_cons, List.length_nil]

theorem innerTail_length (start : Nat) : (innerTail start).length = 32 := by
  simp only [innerTail, updateFlag, incrementWorkspace, loadWorkspace, storeWorkspace,
    loadCell, jumpTo, List.length_append, List.length_cons, List.length_nil]

theorem finishCandidate_length (start : Nat) : (finishCandidate start).length = 34 := by
  simp only [finishCandidate, storeKeep, incrementWorkspace, loadWorkspace, storeWorkspace,
    loadCell, jumpTo, List.length_append, List.length_cons, List.length_nil]

theorem programAt_length (start : Nat) : (programAt start).length = 398 := by
  simp only [programAt, List.length_append, beforeCard_length, betweenScans_length,
    RawCandidatePairScan.programAt_length, innerTail_length, finishCandidate_length]

theorem setWorkspace_length (offset value : Nat) : (setWorkspace offset value).length = 6 := by
  simp only [setWorkspace, storeWorkspace, loadCell, List.length_append, List.length_cons, List.length_nil]

theorem testWorkspace_length (counter exit : Nat) : (testWorkspace counter exit).length = 13 := by
  simp only [testWorkspace, loadWorkspace, loadCell, List.length_append, List.length_cons, List.length_nil]

theorem cardArguments_length : cardArguments.length = 10 := by
  simp only [cardArguments, loadWorkspace, loadCell, storeCell, setCell,
    List.length_append, List.length_cons, List.length_nil]

theorem afterCard_length : afterCard.length = 26 := by
  simp only [afterCard, storeCard, setInitialFlag, initializeLater, loadCell, storeWorkspace,
    List.length_append, List.length_cons, List.length_nil]

theorem pairArguments_length : pairArguments.length = 14 := by
  simp only [pairArguments, loadWorkspace, loadCell, storeCell,
    List.length_append, List.length_cons, List.length_nil]

def cardAddress (base index : Nat) : Nat := base + 4 + index

def keepAddress (base count index : Nat) : Nat := base + 4 + count + index

def paddingOp : PackingOp := .base (.base (.constant .value 0))

theorem append_slice (left right : List PackingOp) :
    left.length + 398 ≤ (left ++ programAt left.length ++ right).length ∧
      ∀ position < 398,
        (left ++ programAt left.length ++ right).getD (left.length + position) paddingOp =
          (programAt left.length).getD position paddingOp := by
  constructor
  · simp only [List.length_append, programAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ programAt left.length) right paddingOp _ (by
      simp only [List.length_append, programAt_length]; omega),
      List.getD_append_right left (programAt left.length) paddingOp _ (by omega), Nat.add_sub_cancel_left]

private theorem getD_middle (left middle right : List PackingOp) (position : Nat)
    (hp : position < middle.length) :
    (left ++ middle ++ right).getD (left.length + position) paddingOp =
      middle.getD position paddingOp := by
  rw [List.getD_append (left ++ middle) right paddingOp _ (by simp; omega),
    List.getD_append_right left middle paddingOp _ (by omega), Nat.add_sub_cancel_left]

theorem loadWorkspace_values (rom : PhysicalROM) (target : Register) (offset : Nat) (state : NatState) :
    let result := runOps rom (loadWorkspace target offset) state
    result.register target = state.heap (state.heap 8 + offset) ∧ result.heap = state.heap ∧
      result.pc = state.pc + 25 ∧ result.halted = state.halted := by
  cases target <;> simp [loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute,
    Instruction.execute, Nat.add_assoc]

theorem storeWorkspace_heap (rom : PhysicalROM) (offset : Nat) (state : NatState) :
    (runOps rom (storeWorkspace offset) state).heap =
      Function.update state.heap (state.heap 8 + offset) (state.register .total) := by
  simp [storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem setWorkspace_heap (rom : PhysicalROM) (offset value : Nat) (state : NatState) :
    (runOps rom (setWorkspace offset value) state).heap =
      Function.update state.heap (state.heap 8 + offset) value := by
  simp [setWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem incrementWorkspace_heap (rom : PhysicalROM) (offset : Nat) (state : NatState) :
    (runOps rom (incrementWorkspace offset) state).heap =
      Function.update state.heap (state.heap 8 + offset) (state.heap (state.heap 8 + offset) + 1) := by
  simp [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, runOps,
    natExecuteOp, Op.execute, Instruction.execute]

theorem testWorkspace_values (rom : PhysicalROM) (counter exit : Nat) (state : NatState) :
    let result := runOps rom (testWorkspace counter exit) state
    result.heap = state.heap ∧ result.pc =
      (if state.heap (state.heap 8) - state.heap (state.heap 8 + counter) = 0 then 5 * exit else state.pc + 65) ∧
      result.halted = state.halted := by
  simp [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute,
    Instruction.execute, Nat.add_assoc]

theorem cardArguments_values (rom : PhysicalROM) (base : Nat) (state : NatState)
    (hbase : state.heap 8 = base) :
    let result := runOps rom cardArguments state
    result.heap = Function.update (Function.update state.heap 1 (state.heap (base + 1))) 2 0 ∧
      result.pc = state.pc + 50 ∧ result.halted = state.halted := by
  simp [cardArguments, loadWorkspace, loadCell, setCell, storeCell, runOps,
    natExecuteOp, Op.execute, Instruction.execute, hbase, Nat.add_assoc]

theorem pairArguments_values (rom : PhysicalROM) (base : Nat) (state : NatState)
    (hbase : state.heap 8 = base) :
    let result := runOps rom pairArguments state
    result.heap = Function.update (Function.update state.heap 1 (state.heap (base + 1))) 2
      ((Function.update state.heap 1 (state.heap (base + 1))) (base + 2)) ∧
      result.pc = state.pc + 70 ∧ result.halted = state.halted := by
  simp [pairArguments, loadWorkspace, loadCell, storeCell, runOps, natExecuteOp,
    Op.execute, Instruction.execute, hbase, Nat.add_assoc]

theorem storeCard_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom storeCard state).heap =
      Function.update state.heap (cardAddress (state.heap 8) (state.heap 1)) (state.heap 4) := by
  simp [storeCard, loadCell, cardAddress, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem updateFlag_heap (rom : PhysicalROM) (base : Nat) (state : NatState)
    (hbase : state.heap 8 = base) :
    (runOps rom updateFlag state).heap = Function.update state.heap (base + 3)
      (if state.heap 5 + state.heap 6 = 0 then 0 else state.heap (base + 3)) := by
  simp [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp,
    Op.execute, Instruction.execute, hbase]

theorem storeKeep_heap (rom : PhysicalROM) (base : Nat) (state : NatState)
    (hbase : state.heap 8 = base) :
    (runOps rom storeKeep state).heap =
      Function.update state.heap (keepAddress base (state.heap base) (state.heap 1)) (state.heap (base + 3)) := by
  simp [storeKeep, loadWorkspace, loadCell, keepAddress, runOps, natExecuteOp,
    Op.execute, Instruction.execute, hbase, Nat.add_assoc]

theorem afterCard_heap (rom : PhysicalROM) (base : Nat) (state : NatState)
    (hbase : state.heap 8 = base) (hlarge : 16 ≤ base) :
    (runOps rom afterCard state).heap =
      Function.update (Function.update (Function.update state.heap
        (cardAddress base (state.heap 1)) (state.heap 4)) (base + 3) (min 1 (state.heap 4)))
        (base + 2) (state.heap 1 + 1) := by
  have hc8 : 8 ≠ base + 4 + state.heap 1 := by omega
  have hc1 : 1 ≠ base + 4 + state.heap 1 := by omega
  have hf8 : 8 ≠ base + 3 := by omega
  simp [afterCard, storeCard, setInitialFlag, initializeLater, storeWorkspace, loadCell,
    cardAddress, runOps, natExecuteOp, Op.execute, Instruction.execute,
    hbase, hc8, hc1, hf8]

theorem innerTail_heap (rom : PhysicalROM) (start base : Nat) (state : NatState)
    (hbase : state.heap 8 = base) (hlarge : 16 ≤ base) :
    (runOps rom (innerTail start) state).heap =
      Function.update (Function.update state.heap (base + 3)
        (if state.heap 5 + state.heap 6 = 0 then 0 else state.heap (base + 3)))
        (base + 2) (state.heap (base + 2) + 1) := by
  have hf8 : 8 ≠ base + 3 := by omega
  simp [innerTail, updateFlag, incrementWorkspace, loadWorkspace, storeWorkspace,
    loadCell, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute,
    hbase, hf8]

theorem innerTail_control (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (innerTail start) state).pc = 5 * (start + 180) ∧
      (runOps rom (innerTail start) state).halted = state.halted := by
  constructor
  · simp [innerTail, updateFlag, incrementWorkspace, loadWorkspace, storeWorkspace,
      loadCell, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · exact runOps_halted _ _ _

theorem finishCandidate_heap (rom : PhysicalROM) (start base : Nat) (state : NatState)
    (hbase : state.heap 8 = base) (hlarge : 16 ≤ base) :
    (runOps rom (finishCandidate start) state).heap =
      Function.update (Function.update state.heap
        (keepAddress base (state.heap base) (state.heap 1)) (state.heap (base + 3)))
        (base + 1) (state.heap (base + 1) + 1) := by
  have hk8 : 8 ≠ base + (4 + (state.heap base + state.heap 1)) := by omega
  have hk1 : 1 ≠ 4 + (state.heap base + state.heap 1) := by omega
  simp [finishCandidate, storeKeep, incrementWorkspace, loadWorkspace, storeWorkspace,
    loadCell, jumpTo, keepAddress, runOps, natExecuteOp, Op.execute, Instruction.execute,
    hbase, hk8, hk1, Nat.add_assoc]

theorem finishCandidate_control (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (finishCandidate start) state).pc = 5 * (start + 6) ∧
      (runOps rom (finishCandidate start) state).halted = state.halted := by
  constructor
  · simp [finishCandidate, storeKeep, incrementWorkspace, loadWorkspace, storeWorkspace,
      loadCell, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · exact runOps_halted _ _ _

theorem min_one_card (q : Nat) (support : Finset (Fin q)) :
    min 1 support.card = bit (decide support.Nonempty) := by
  by_cases hn : support.Nonempty
  · simp [bit, hn]
  · have hz : support.card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.not_nonempty_iff_eq_empty.mp hn
    simp [bit, hn, hz]

section Containing

variable (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp =
    (programAt start).getD position paddingOp)

include hbound hcode

private theorem run_straight (offset : Nat) (block : List PackingOp)
    (hspan : offset + block.length ≤ 398)
    (hlocal : ∀ position < block.length,
      (programAt start).getD (offset + position) paddingOp = block.getD position paddingOp)
    (hstraight : ∀ op ∈ block, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing block.length state = runOps rom block state := by
  apply natRun_of_straight_segment rom containing block (start + offset) (by omega) ?_
    hstraight state hpc hactive
  intro position hp
  have hh := (hcode (offset + position) (by omega)).trans (hlocal position hp)
  rw [List.getD_eq_getElem containing paddingOp (by omega),
    List.getD_eq_getElem block paddingOp hp] at hh
  simpa only [Nat.add_assoc] using hh

private theorem run_branch (offset : Nat) (lead : List PackingOp) (last : PackingOp)
    (hspan : offset + lead.length + 1 ≤ 398)
    (hlocal : ∀ position < lead.length,
      (programAt start).getD (offset + position) paddingOp = lead.getD position paddingOp)
    (hlast : (programAt start).getD (offset + lead.length) paddingOp = last)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing (lead.length + 1) state = runOps rom (lead ++ [last]) state := by
  rw [runOps_append, runOps]
  apply natRun_of_segment_last rom containing lead last (start + offset) (by omega) ?_ ?_
    hstraight state hpc hactive
  · intro position hp
    have hh := (hcode (offset + position) (by omega)).trans (hlocal position hp)
    rw [List.getD_eq_getElem containing paddingOp (by omega),
      List.getD_eq_getElem lead paddingOp hp] at hh
    simpa only [Nat.add_assoc] using hh
  · have hh := (hcode (offset + lead.length) (by omega)).trans hlast
    rw [List.getD_eq_getElem containing paddingOp (by omega)] at hh
    simpa only [Nat.add_assoc] using hh

private theorem run_straight_piece (offset : Nat) (codePrefix block suffix : List PackingOp)
    (hsplit : programAt start = codePrefix ++ block ++ suffix) (hlength : codePrefix.length = offset)
    (hstraight : ∀ op ∈ block, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing block.length state = runOps rom block state := by
  have hlen : offset + block.length + suffix.length = 398 := by
    rw [← programAt_length start, hsplit, List.length_append, List.length_append, hlength]
  apply run_straight rom containing start hbound hcode offset block (by omega) ?_
    hstraight state hpc hactive
  intro position hp
  rw [hsplit]
  have hh := getD_middle codePrefix block suffix position hp
  rw [hlength] at hh
  exact hh

private theorem run_branch_piece (offset : Nat) (codePrefix lead suffix : List PackingOp) (last : PackingOp)
    (hsplit : programAt start = codePrefix ++ (lead ++ [last]) ++ suffix) (hlength : codePrefix.length = offset)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing (lead.length + 1) state = runOps rom (lead ++ [last]) state := by
  have hlen : offset + (lead.length + 1) + suffix.length = 398 := by
    rw [← programAt_length start, hsplit, List.length_append, List.length_append, hlength,
      List.length_append, List.length_singleton]
  apply run_branch rom containing start hbound hcode offset lead last (by omega) ?_ ?_
    hstraight state hpc hactive
  · intro position hp
    rw [hsplit]
    have hh := getD_middle codePrefix (lead ++ [last]) suffix position (by simp; omega)
    rw [hlength, List.getD_append lead [last] paddingOp position hp] at hh
    exact hh
  · rw [hsplit]
    have hh := getD_middle codePrefix (lead ++ [last]) suffix lead.length (by simp)
    rw [hlength, List.getD_append_right lead [last] paddingOp lead.length le_rfl,
      Nat.sub_self, List.getD_cons_zero] at hh
    exact hh

private theorem run_init (state : NatState)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    natRun rom containing 6 state = runOps rom (setWorkspace 1 0) state := by
  exact run_straight_piece rom containing start hbound hcode 0 [] (setWorkspace 1 0)
    (testWorkspace 1 (start + 398) ++ cardArguments ++ RawCandidatePairScan.programAt (start + 29) ++
      betweenScans start ++ RawCandidatePairScan.programAt (start + 207) ++ innerTail start ++ finishCandidate start)
    (by simp only [programAt, beforeCard, List.nil_append, List.append_assoc]) rfl
    (by simp [setWorkspace, storeWorkspace, loadCell, NoJump]) state
    (by simpa only [Nat.add_zero] using hpc) hactive

private theorem run_outerTest (state : NatState)
    (hpc : state.pc = 5 * (start + 6)) (hactive : state.halted = false) :
    natRun rom containing 13 state = runOps rom (testWorkspace 1 (start + 398)) state := by
  have hs : testWorkspace 1 (start + 398) =
      (testWorkspace 1 (start + 398)).take 12 ++ [.jumpIfZero .flag .index] := by
    rfl
  exact run_branch_piece rom containing start hbound hcode 6 (setWorkspace 1 0)
    ((testWorkspace 1 (start + 398)).take 12)
    (cardArguments ++ RawCandidatePairScan.programAt (start + 29) ++ betweenScans start ++
      RawCandidatePairScan.programAt (start + 207) ++ innerTail start ++ finishCandidate start)
    (.jumpIfZero .flag .index)
    (by rw [← hs]; simp only [programAt, beforeCard, List.append_assoc]) (setWorkspace_length 1 0)
    (by simp [testWorkspace, loadWorkspace, loadCell, NoJump]) state hpc hactive

private theorem run_cardArguments (state : NatState)
    (hpc : state.pc = 5 * (start + 19)) (hactive : state.halted = false) :
    natRun rom containing 10 state = runOps rom cardArguments state := by
  exact run_straight_piece rom containing start hbound hcode 19
    (setWorkspace 1 0 ++ testWorkspace 1 (start + 398)) cardArguments
    (RawCandidatePairScan.programAt (start + 29) ++ betweenScans start ++
      RawCandidatePairScan.programAt (start + 207) ++ innerTail start ++ finishCandidate start)
    (by simp only [programAt, beforeCard, List.append_assoc])
    (by simp only [List.length_append, setWorkspace_length, testWorkspace_length])
    (by simp [cardArguments, loadWorkspace, loadCell, setCell, storeCell, NoJump]) state hpc hactive

private theorem run_afterCard (state : NatState)
    (hpc : state.pc = 5 * (start + 154)) (hactive : state.halted = false) :
    natRun rom containing 26 state = runOps rom afterCard state := by
  exact run_straight_piece rom containing start hbound hcode 154
    (beforeCard start ++ RawCandidatePairScan.programAt (start + 29)) afterCard
    (testWorkspace 2 (start + 364) ++ pairArguments ++ RawCandidatePairScan.programAt (start + 207) ++
      innerTail start ++ finishCandidate start)
    (by simp only [programAt, betweenScans, List.append_assoc])
    (by simp only [List.length_append, beforeCard_length, RawCandidatePairScan.programAt_length])
    (by simp [afterCard, storeCard, setInitialFlag, initializeLater, loadCell, storeWorkspace, NoJump])
    state hpc hactive

private theorem run_innerTest (state : NatState)
    (hpc : state.pc = 5 * (start + 180)) (hactive : state.halted = false) :
    natRun rom containing 13 state = runOps rom (testWorkspace 2 (start + 364)) state := by
  have hs : testWorkspace 2 (start + 364) =
      (testWorkspace 2 (start + 364)).take 12 ++ [.jumpIfZero .flag .index] := by
    rfl
  exact run_branch_piece rom containing start hbound hcode 180
    (beforeCard start ++ RawCandidatePairScan.programAt (start + 29) ++ afterCard)
    ((testWorkspace 2 (start + 364)).take 12)
    (pairArguments ++ RawCandidatePairScan.programAt (start + 207) ++ innerTail start ++ finishCandidate start)
    (.jumpIfZero .flag .index)
    (by rw [← hs]; simp only [programAt, betweenScans, List.append_assoc])
    (by simp only [List.length_append, beforeCard_length, RawCandidatePairScan.programAt_length, afterCard_length])
    (by simp [testWorkspace, loadWorkspace, loadCell, NoJump]) state hpc hactive

private theorem run_pairArguments (state : NatState)
    (hpc : state.pc = 5 * (start + 193)) (hactive : state.halted = false) :
    natRun rom containing 14 state = runOps rom pairArguments state := by
  exact run_straight_piece rom containing start hbound hcode 193
    (beforeCard start ++ RawCandidatePairScan.programAt (start + 29) ++
      afterCard ++ testWorkspace 2 (start + 364)) pairArguments
    (RawCandidatePairScan.programAt (start + 207) ++ innerTail start ++ finishCandidate start)
    (by simp only [programAt, betweenScans, List.append_assoc])
    (by simp only [List.length_append, beforeCard_length, RawCandidatePairScan.programAt_length,
      afterCard_length, testWorkspace_length])
    (by simp [pairArguments, loadWorkspace, loadCell, storeCell, NoJump]) state hpc hactive

private theorem run_innerTail (state : NatState)
    (hpc : state.pc = 5 * (start + 332)) (hactive : state.halted = false) :
    natRun rom containing 32 state = runOps rom (innerTail start) state := by
  have hs : innerTail start = (innerTail start).take 31 ++ [.jumpIfZero .flag .index] := by
    rfl
  exact run_branch_piece rom containing start hbound hcode 332
    (beforeCard start ++ RawCandidatePairScan.programAt (start + 29) ++ betweenScans start ++
      RawCandidatePairScan.programAt (start + 207)) ((innerTail start).take 31)
    (finishCandidate start) (.jumpIfZero .flag .index)
    (by rw [← hs]; simp only [programAt, List.append_assoc])
    (by simp only [List.length_append, beforeCard_length, RawCandidatePairScan.programAt_length, betweenScans_length])
    (by simp [innerTail, updateFlag, incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, jumpTo, NoJump])
    state hpc hactive

private theorem run_finishCandidate (state : NatState)
    (hpc : state.pc = 5 * (start + 364)) (hactive : state.halted = false) :
    natRun rom containing 34 state = runOps rom (finishCandidate start) state := by
  have hs : finishCandidate start = (finishCandidate start).take 33 ++ [.jumpIfZero .flag .index] := by
    rfl
  exact run_branch_piece rom containing start hbound hcode 364
    (beforeCard start ++ RawCandidatePairScan.programAt (start + 29) ++ betweenScans start ++
      RawCandidatePairScan.programAt (start + 207) ++ innerTail start) ((finishCandidate start).take 33)
    [] (.jumpIfZero .flag .index)
    (by rw [← hs]; simp only [programAt, List.append_nil, List.append_assoc])
    (by simp only [List.length_append, beforeCard_length, RawCandidatePairScan.programAt_length,
      betweenScans_length, innerTail_length])
    (by simp [finishCandidate, storeKeep, incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, jumpTo, NoJump])
    state hpc hactive

end Containing

section PairCalls

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp =
    (programAt start).getD position paddingOp)

include hbound hcode

private theorem pair_slice (offset : Nat) (hoffset : offset = 29 ∨ offset = 207) :
    start + offset + 125 ≤ containing.length ∧
      ∀ position < 125, containing.getD ((start + offset) + position) paddingOp =
        (RawCandidatePairScan.programAt (start + offset)).getD position paddingOp := by
  have hoff : offset + 125 ≤ 398 := by rcases hoffset with rfl | rfl <;> omega
  constructor
  · omega
  · intro position hp
    have hlocal : (programAt start).getD (offset + position) paddingOp =
        (RawCandidatePairScan.programAt (start + offset)).getD position paddingOp := by
      rcases hoffset with rfl | rfl
      · let suffix := betweenScans start ++ RawCandidatePairScan.programAt (start + 207) ++
          innerTail start ++ finishCandidate start
        have heq : programAt start = beforeCard start ++ RawCandidatePairScan.programAt (start + 29) ++ suffix := by
          simp only [programAt, suffix, List.append_assoc]
        have hh := getD_middle (beforeCard start) (RawCandidatePairScan.programAt (start + 29))
          suffix position (by rw [RawCandidatePairScan.programAt_length]; exact hp)
        rw [beforeCard_length] at hh
        rw [heq]
        exact hh
      · let codePrefix := beforeCard start ++ RawCandidatePairScan.programAt (start + 29) ++ betweenScans start
        have hlength : codePrefix.length = 207 := by
          simp only [codePrefix, List.length_append, beforeCard_length, betweenScans_length,
            RawCandidatePairScan.programAt_length]
        have heq : programAt start = codePrefix ++ RawCandidatePairScan.programAt (start + 207) ++
            (innerTail start ++ finishCandidate start) := by
          simp only [programAt, codePrefix, List.append_assoc]
        have hh := getD_middle codePrefix (RawCandidatePairScan.programAt (start + 207))
          (innerTail start ++ finishCandidate start) position
          (by rw [RawCandidatePairScan.programAt_length]; exact hp)
        rw [hlength] at hh
        rw [heq]
        exact hh
    have hh := (hcode (offset + position) (by omega)).trans hlocal
    simpa only [Nat.add_assoc] using hh

private theorem pair_call (offset : Nat) (hoffset : offset = 29 ∨ offset = 207)
    (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val) :
    let L := (RawCandidateOrder.candidateSupports q full).getD left.val ∅
    let R := (RawCandidateOrder.candidateSupports q full).getD right.val ∅
    let result := natRun (rawIncidenceROM q full) containing
      (RawCandidatePairScan.totalSteps full.length left.val right.val q) state
    result.heap 4 = (L ∩ R).card ∧ result.heap 5 = (L \ R).card ∧ result.heap 6 = (R \ L).card ∧
      result.heap 1 = left.val ∧ result.heap 2 = right.val ∧
      (∀ address, 8 ≤ address → result.heap address = state.heap address) ∧
      result.pc = 5 * (start + offset + 125) ∧ result.halted = false := by
  obtain ⟨hspan, hslice⟩ := pair_slice containing start hbound hcode offset hoffset
  have hs := RawCandidatePairScan.scan q full containing (start + offset) hspan hslice
    left right state hpc hactive hl hr
  dsimp only at hs ⊢
  rcases hs with ⟨_, _, h4, h5, h6, hframe, hp, ha⟩
  refine ⟨h4, h5, h6, ?_, ?_, ?_, hp, ha⟩
  · exact (hframe 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
  · exact (hframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr
  · intro address haddr
    exact hframe address (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

end PairCalls

def innerIterationSteps (N q index later : Nat) : Nat :=
  59 + RawCandidatePairScan.totalSteps N index later q

theorem inner_iteration (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 398 ≤ containing.length)
    (hcode : ∀ position < 398, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base index later : Nat) (hlarge : 16 ≤ base)
    (hi : index < full.length + q + 1) (hj : later < full.length + q + 1)
    (state : NatState) (hbase : state.heap 8 = base)
    (hcount : state.heap base = full.length + q + 1)
    (hindex : state.heap (base + 1) = index) (hlater : state.heap (base + 2) = later)
    (hpc : state.pc = 5 * (start + 180)) (hactive : state.halted = false) :
    let L := (RawCandidateOrder.candidateSupports q full).getD index ∅
    let R := (RawCandidateOrder.candidateSupports q full).getD later ∅
    let result := natRun (rawIncidenceROM q full) containing
      (innerIterationSteps full.length q index later) state
    result.heap (base + 2) = later + 1 ∧
      result.heap (base + 3) =
        (if (L \ R).card + (R \ L).card = 0 then 0 else state.heap (base + 3)) ∧
      result.heap 1 = index ∧
      (∀ address, 8 ≤ address → address ≠ base + 2 → address ≠ base + 3 →
        result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 180) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (testWorkspace 2 (start + 364)) state
  have ht := testWorkspace_values rom 2 (start + 364) state
  have htestHeap : tested.heap = state.heap := ht.1
  have htestPc : tested.pc = 5 * (start + 193) := by
    have hp := ht.2.1
    rw [hbase, hcount, hlater] at hp
    simp only [Nat.sub_ne_zero_of_lt hj, ite_false, hpc] at hp
    change tested.pc = _ at hp
    omega
  have htestActive : tested.halted = false := ht.2.2.trans hactive
  let arguments := runOps rom pairArguments tested
  have hargs := pairArguments_values rom base tested (by rw [htestHeap]; exact hbase)
  have hB2 : base + 2 ≠ 1 := by omega
  have hargHeap : arguments.heap = Function.update (Function.update state.heap 1 index) 2 later := by
    simpa only [htestHeap, hindex, Function.update_of_ne hB2, hlater] using hargs.1
  have hargAbove (address : Nat) (haddr : 8 ≤ address) : arguments.heap address = state.heap address := by
    rw [hargHeap]
    simp [show address ≠ 1 by omega, show address ≠ 2 by omega]
  have hargPc : arguments.pc = 5 * (start + 207) := by
    have hp := hargs.2.1
    rw [htestPc] at hp
    change arguments.pc = _ at hp
    omega
  have hargActive : arguments.halted = false := hargs.2.2.trans htestActive
  let scanned := natRun rom containing (RawCandidatePairScan.totalSteps full.length index later q) arguments
  have hs := pair_call q full containing start hbound hcode 207 (Or.inr rfl)
    ⟨index, hi⟩ ⟨later, hj⟩ arguments hargPc hargActive
    (by rw [hargHeap]; simp) (by rw [hargHeap]; simp)
  dsimp only at hs
  rcases hs with ⟨_, hs5, hs6, hs1, _, hsframe, hsp, hsa⟩
  have hscannedBase : scanned.heap 8 = base := (hsframe 8 le_rfl).trans ((hargAbove 8 le_rfl).trans hbase)
  have hscannedLater : scanned.heap (base + 2) = later :=
    (hsframe (base + 2) (by omega)).trans ((hargAbove (base + 2) (by omega)).trans hlater)
  have hscannedFlag : scanned.heap (base + 3) = state.heap (base + 3) :=
    (hsframe (base + 3) (by omega)).trans (hargAbove (base + 3) (by omega))
  have hbody : natRun rom containing (innerIterationSteps full.length q index later) state =
      runOps rom (innerTail start) scanned := by
    rw [show innerIterationSteps full.length q index later =
        13 + (14 + (RawCandidatePairScan.totalSteps full.length index later q + 32)) by
          unfold innerIterationSteps; omega,
      natRun_add, run_innerTest rom containing start hbound hcode state hpc hactive]
    change natRun rom containing (14 + (RawCandidatePairScan.totalSteps full.length index later q + 32)) tested = _
    rw [natRun_add, run_pairArguments rom containing start hbound hcode tested htestPc htestActive, natRun_add]
    exact run_innerTail rom containing start hbound hcode scanned (by omega) hsa
  have hheap := innerTail_heap rom start base scanned hscannedBase hlarge
  have hc := innerTail_control rom start scanned
  dsimp only
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [hbody]
  refine ⟨?_, ?_, ?_, ?_, hc.1, hc.2.trans hsa⟩
  · rw [hheap, hscannedLater]
    simp
  · rw [hheap, hs5, hs6, hscannedFlag]
    simp
  · rw [hheap]
    simpa [show 1 ≠ base + 2 by omega, show 1 ≠ base + 3 by omega] using hs1
  · intro address haddr h2 h3
    rw [hheap]
    simp only [Function.update_of_ne h2, Function.update_of_ne h3]
    exact (hsframe address haddr).trans (hargAbove address haddr)

def innerScanSteps (N q index first count : Nat) : Nat :=
  ∑ offset ∈ Finset.range count, innerIterationSteps N q index (first + offset)

theorem innerScanSteps_succ (N q index first count : Nat) :
    innerScanSteps N q index first (count + 1) = innerScanSteps N q index first count +
      innerIterationSteps N q index (first + count) := Finset.sum_range_succ _ _

theorem inner_scan_partial (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 398 ≤ containing.length)
    (hcode : ∀ position < 398, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base index first : Nat) (hlarge : 16 ≤ base)
    (hi : index < full.length + q + 1) (hfirst : index < first)
    (state : NatState) (hbase : state.heap 8 = base)
    (hcount : state.heap base = full.length + q + 1)
    (hindex : state.heap (base + 1) = index) (hlater : state.heap (base + 2) = first)
    (hraw : state.heap 1 = index)
    (hflag : state.heap (base + 3) = RawCandidateRetentionFlags.partialFlag q full index first)
    (hpc : state.pc = 5 * (start + 180)) (hactive : state.halted = false)
    (count : Nat) (hwithin : first + count ≤ full.length + q + 1) :
    let result := natRun (rawIncidenceROM q full) containing
      (innerScanSteps full.length q index first count) state
    result.heap (base + 2) = first + count ∧
      result.heap (base + 3) = RawCandidateRetentionFlags.partialFlag q full index (first + count) ∧
      result.heap 1 = index ∧
      (∀ address, 8 ≤ address → address ≠ base + 2 → address ≠ base + 3 →
        result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 180) ∧ result.halted = false := by
  revert hwithin
  induction count with
  | zero =>
    intro _
    simpa only [innerScanSteps, Finset.range_zero, Finset.sum_empty, natRun, Nat.add_zero] using
      (show state.heap (base + 2) = first ∧
        state.heap (base + 3) = RawCandidateRetentionFlags.partialFlag q full index first ∧
        state.heap 1 = index ∧
        (∀ address, 8 ≤ address → address ≠ base + 2 → address ≠ base + 3 → state.heap address = state.heap address) ∧
        state.pc = 5 * (start + 180) ∧ state.halted = false from
          ⟨hlater, hflag, hraw, fun _ _ _ _ => rfl, hpc, hactive⟩)
  | succ count ih =>
    intro hwithin
    rcases ih (by omega) with ⟨hj, hf, hraw', hframe, hp, ha⟩
    let previous := natRun (rawIncidenceROM q full) containing
      (innerScanSteps full.length q index first count) state
    have hb' : previous.heap 8 = base :=
      (hframe 8 le_rfl (by omega) (by omega)).trans hbase
    have hm' : previous.heap base = full.length + q + 1 :=
      (hframe base (by omega) (by omega) (by omega)).trans hcount
    have hi' : previous.heap (base + 1) = index :=
      (hframe (base + 1) (by omega) (by omega) (by omega)).trans hindex
    have hs := inner_iteration q full containing start hbound hcode base index (first + count)
      hlarge hi (by omega) previous hb' hm' hi' hj hp ha
    dsimp only at hs
    rcases hs with ⟨hsj, hsf, hsr, hsframe, hsp, hsa⟩
    have hstep := RawCandidateRetentionFlags.partialFlag_step_of_differenceCount q full index
      (first + count) (by omega)
    rw [show previous.heap (base + 3) = _ from hf] at hsf
    have hsf' : (natRun (rawIncidenceROM q full) containing
        (innerIterationSteps full.length q index (first + count)) previous).heap (base + 3) =
        RawCandidateRetentionFlags.partialFlag q full index (first + count + 1) := by
      exact hsf.trans hstep.symm
    have hrun : natRun (rawIncidenceROM q full) containing
        (innerScanSteps full.length q index first (count + 1)) state =
        natRun (rawIncidenceROM q full) containing
          (innerIterationSteps full.length q index (first + count)) previous := by
      rw [innerScanSteps_succ, natRun_add]
    dsimp only
    rw [hrun]
    refine ⟨?_, ?_, hsr, ?_, hsp, hsa⟩
    · simpa only [Nat.add_assoc] using hsj
    · simpa only [Nat.add_assoc] using hsf'
    · intro address haddr h2 h3
      exact (hsframe address haddr h2 h3).trans (hframe address haddr h2 h3)

def innerCompleteSteps (N q index : Nat) : Nat :=
  innerScanSteps N q index (index + 1) (N + q + 1 - (index + 1)) + 13

theorem inner_scan (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 398 ≤ containing.length)
    (hcode : ∀ position < 398, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base index : Nat) (hlarge : 16 ≤ base) (hi : index < full.length + q + 1)
    (state : NatState) (hbase : state.heap 8 = base)
    (hcount : state.heap base = full.length + q + 1)
    (hindex : state.heap (base + 1) = index) (hlater : state.heap (base + 2) = index + 1)
    (hraw : state.heap 1 = index)
    (hflag : state.heap (base + 3) = RawCandidateRetentionFlags.partialFlag q full index (index + 1))
    (hpc : state.pc = 5 * (start + 180)) (hactive : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (innerCompleteSteps full.length q index) state
    result.heap (base + 2) = full.length + q + 1 ∧
      result.heap (base + 3) = bit (RawCandidateOrder.keepCandidate q full index) ∧
      result.heap 1 = index ∧
      (∀ address, 8 ≤ address → address ≠ base + 2 → address ≠ base + 3 →
        result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 364) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let count := full.length + q + 1 - (index + 1)
  have hsum : index + 1 + count = full.length + q + 1 := by dsimp [count]; omega
  have hs := inner_scan_partial q full containing start hbound hcode base index (index + 1)
    hlarge hi (by omega) state hbase hcount hindex hlater hraw hflag hpc hactive count (by omega)
  dsimp only at hs
  rw [hsum, RawCandidateRetentionFlags.partialFlag_full] at hs
  rcases hs with ⟨hj, hf, hr, hframe, hp, ha⟩
  let previous := natRun rom containing (innerScanSteps full.length q index (index + 1) count) state
  have hb' : previous.heap 8 = base := (hframe 8 le_rfl (by omega) (by omega)).trans hbase
  have hm' : previous.heap base = full.length + q + 1 :=
    (hframe base (by omega) (by omega) (by omega)).trans hcount
  have ht := testWorkspace_values rom 2 (start + 364) previous
  have hrun : natRun rom containing (innerCompleteSteps full.length q index) state =
      runOps rom (testWorkspace 2 (start + 364)) previous := by
    rw [innerCompleteSteps, natRun_add]
    exact run_innerTest rom containing start hbound hcode previous hp ha
  dsimp only
  rw [hrun]
  refine ⟨(congrFun ht.1 (base + 2)).trans hj, (congrFun ht.1 (base + 3)).trans hf,
    (congrFun ht.1 1).trans hr, ?_, ?_, ht.2.2.trans ha⟩
  · intro address haddr h2 h3
    exact (congrFun ht.1 address).trans (hframe address haddr h2 h3)
  · have htestPc := ht.2.1
    rw [hb', hm', show previous.heap (base + 2) = full.length + q + 1 from hj,
      Nat.sub_self] at htestPc
    exact htestPc

theorem innerIterationSteps_le (N q index later : Nat) :
    innerIterationSteps N q index later ≤ 87 * q + 82 := by
  have h := RawCandidatePairScan.totalSteps_le N index later q
  unfold innerIterationSteps
  omega

theorem innerScanSteps_le (N q index first count : Nat) :
    innerScanSteps N q index first count ≤ count * (87 * q + 82) := by
  unfold innerScanSteps
  calc
    _ ≤ ∑ _offset ∈ Finset.range count, (87 * q + 82) :=
      Finset.sum_le_sum (fun offset _ => innerIterationSteps_le N q index (first + offset))
    _ = _ := by simp [Nat.mul_comm]

def cardPhaseSteps (N q index : Nat) : Nat := 49 + RawCandidatePairScan.totalSteps N index 0 q

theorem card_phase (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 398 ≤ containing.length)
    (hcode : ∀ position < 398, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base index : Nat) (hlarge : 16 ≤ base) (hi : index < full.length + q + 1)
    (state : NatState) (hbase : state.heap 8 = base)
    (hcount : state.heap base = full.length + q + 1) (hindex : state.heap (base + 1) = index)
    (hpc : state.pc = 5 * (start + 6)) (hactive : state.halted = false) :
    let L := (RawCandidateOrder.candidateSupports q full).getD index ∅
    let result := natRun (rawIncidenceROM q full) containing (cardPhaseSteps full.length q index) state
    result.heap (base + 2) = index + 1 ∧
      result.heap (base + 3) = RawCandidateRetentionFlags.partialFlag q full index (index + 1) ∧
      result.heap 1 = index ∧ result.heap (cardAddress base index) = L.card ∧
      (∀ address, 8 ≤ address → address ≠ base + 2 → address ≠ base + 3 →
        address ≠ cardAddress base index → result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 180) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (testWorkspace 1 (start + 398)) state
  have ht := testWorkspace_values rom 1 (start + 398) state
  have htestHeap : tested.heap = state.heap := ht.1
  have htestPc : tested.pc = 5 * (start + 19) := by
    have hp := ht.2.1
    rw [hbase, hcount, hindex] at hp
    simp only [Nat.sub_ne_zero_of_lt hi, ite_false, hpc] at hp
    change tested.pc = _ at hp
    omega
  have htestActive : tested.halted = false := ht.2.2.trans hactive
  let arguments := runOps rom cardArguments tested
  have hargs := cardArguments_values rom base tested (by rw [htestHeap]; exact hbase)
  have hargHeap : arguments.heap = Function.update (Function.update state.heap 1 index) 2 0 := by
    simpa only [htestHeap, hindex] using hargs.1
  have hargAbove (address : Nat) (haddr : 8 ≤ address) : arguments.heap address = state.heap address := by
    rw [hargHeap]
    simp [show address ≠ 1 by omega, show address ≠ 2 by omega]
  have hargPc : arguments.pc = 5 * (start + 29) := by
    have hp := hargs.2.1
    rw [htestPc] at hp
    change arguments.pc = _ at hp
    omega
  have hargActive : arguments.halted = false := hargs.2.2.trans htestActive
  let scanned := natRun rom containing (RawCandidatePairScan.totalSteps full.length index 0 q) arguments
  have hs := pair_call q full containing start hbound hcode 29 (Or.inl rfl)
    ⟨index, hi⟩ ⟨0, by omega⟩ arguments hargPc hargActive
    (by rw [hargHeap]; simp) (by rw [hargHeap]; simp)
  dsimp only at hs
  have hroot : (RawCandidateOrder.candidateSupports q full).getD 0 ∅ = Finset.univ := rfl
  rw [hroot, Finset.inter_univ] at hs
  rcases hs with ⟨hs4, _, _, hs1, _, hsframe, hsp, hsa⟩
  have hscannedBase : scanned.heap 8 = base := (hsframe 8 le_rfl).trans ((hargAbove 8 le_rfl).trans hbase)
  have hscannedAbove (address : Nat) (haddr : 8 ≤ address) : scanned.heap address = state.heap address :=
    (hsframe address haddr).trans (hargAbove address haddr)
  have hbody : natRun rom containing (cardPhaseSteps full.length q index) state =
      runOps rom afterCard scanned := by
    rw [show cardPhaseSteps full.length q index =
        13 + (10 + (RawCandidatePairScan.totalSteps full.length index 0 q + 26)) by unfold cardPhaseSteps; omega,
      natRun_add, run_outerTest rom containing start hbound hcode state hpc hactive]
    change natRun rom containing (10 + (RawCandidatePairScan.totalSteps full.length index 0 q + 26)) tested = _
    rw [natRun_add, run_cardArguments rom containing start hbound hcode tested htestPc htestActive, natRun_add]
    exact run_afterCard rom containing start hbound hcode scanned (by omega) hsa
  have hheap := afterCard_heap rom base scanned hscannedBase hlarge
  rw [show scanned.heap 1 = index from hs1, show scanned.heap 4 = _ from hs4] at hheap
  have hpcAfter : (runOps rom afterCard scanned).pc = 5 * (start + 180) := by
    rw [runOps_pc rom afterCard scanned (by
      simp [afterCard, storeCard, setInitialFlag, initializeLater, loadCell, storeWorkspace, NoJump]),
      afterCard_length, show scanned.pc = 5 * (start + 29 + 125) from hsp]
    omega
  have hseed : min 1 ((RawCandidateOrder.candidateSupports q full).getD index ∅).card =
      RawCandidateRetentionFlags.partialFlag q full index (index + 1) := by
    rw [RawCandidateRetentionFlags.partialFlag_initial]
    exact min_one_card q _
  dsimp only
  rw [hbody]
  refine ⟨?_, ?_, ?_, ?_, ?_, hpcAfter, (runOps_halted _ _ _).trans hsa⟩
  · rw [hheap]
    simp
  · rw [hheap]
    simpa using hseed
  · rw [hheap]
    simpa [cardAddress, show 1 ≠ base + 2 by omega, show 1 ≠ base + 3 by omega,
      show 1 ≠ base + 4 + index by omega] using hs1
  · rw [hheap]
    simp [cardAddress, show base + 4 + index ≠ base + 2 by omega,
      show base + 4 + index ≠ base + 3 by omega]
  · intro address haddr h2 h3 hc
    rw [hheap]
    simp only [Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne hc]
    exact hscannedAbove address haddr

def outerIterationSteps (N q index : Nat) : Nat :=
  cardPhaseSteps N q index + innerCompleteSteps N q index + 34

theorem outer_iteration (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 398 ≤ containing.length)
    (hcode : ∀ position < 398, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base index : Nat) (hlarge : 16 ≤ base) (hi : index < full.length + q + 1)
    (state : NatState) (hbase : state.heap 8 = base)
    (hcount : state.heap base = full.length + q + 1) (hindex : state.heap (base + 1) = index)
    (hpc : state.pc = 5 * (start + 6)) (hactive : state.halted = false) :
    let L := (RawCandidateOrder.candidateSupports q full).getD index ∅
    let result := natRun (rawIncidenceROM q full) containing (outerIterationSteps full.length q index) state
    result.heap (base + 1) = index + 1 ∧ result.heap (cardAddress base index) = L.card ∧
      result.heap (keepAddress base (full.length + q + 1) index) = bit (RawCandidateOrder.keepCandidate q full index) ∧
      (∀ address, 8 ≤ address → address ≠ base + 1 → address ≠ base + 2 → address ≠ base + 3 →
        address ≠ cardAddress base index → address ≠ keepAddress base (full.length + q + 1) index →
        result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 6) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let seeded := natRun rom containing (cardPhaseSteps full.length q index) state
  have hs := card_phase q full containing start hbound hcode base index hlarge hi state hbase hcount hindex hpc hactive
  dsimp only at hs
  rcases hs with ⟨hsj, hsf, hsr, hsc, hsframe, hsp, hsa⟩
  have hcard8 : 8 ≠ cardAddress base index := by unfold cardAddress; omega
  have hcardB : base ≠ cardAddress base index := by unfold cardAddress; omega
  have hcardB1 : base + 1 ≠ cardAddress base index := by unfold cardAddress; omega
  have hseedBase : seeded.heap 8 = base :=
    (hsframe 8 le_rfl (by omega) (by omega) hcard8).trans hbase
  have hseedCount : seeded.heap base = full.length + q + 1 :=
    (hsframe base (by omega) (by omega) (by omega) hcardB).trans hcount
  have hseedIndex : seeded.heap (base + 1) = index :=
    (hsframe (base + 1) (by omega) (by omega) (by omega) hcardB1).trans hindex
  let scanned := natRun rom containing (innerCompleteSteps full.length q index) seeded
  have hiScan := inner_scan q full containing start hbound hcode base index hlarge hi seeded
    hseedBase hseedCount hseedIndex hsj hsr hsf hsp hsa
  dsimp only at hiScan
  rcases hiScan with ⟨_, hif, hir, hiframe, hip, hia⟩
  have hscanBase : scanned.heap 8 = base :=
    (hiframe 8 le_rfl (by omega) (by omega)).trans hseedBase
  have hscanCount : scanned.heap base = full.length + q + 1 :=
    (hiframe base (by omega) (by omega) (by omega)).trans hseedCount
  have hscanIndex : scanned.heap (base + 1) = index :=
    (hiframe (base + 1) (by omega) (by omega) (by omega)).trans hseedIndex
  have hscanCard : scanned.heap (cardAddress base index) =
      ((RawCandidateOrder.candidateSupports q full).getD index ∅).card :=
    (hiframe (cardAddress base index) (by unfold cardAddress; omega)
      (by unfold cardAddress; omega) (by unfold cardAddress; omega)).trans hsc
  have hheap := finishCandidate_heap rom start base scanned hscanBase hlarge
  rw [show scanned.heap base = _ from hscanCount, show scanned.heap 1 = index from hir,
    show scanned.heap (base + 3) = _ from hif,
    show scanned.heap (base + 1) = index from hscanIndex] at hheap
  have hc := finishCandidate_control rom start scanned
  have hbody : natRun rom containing (outerIterationSteps full.length q index) state =
      runOps rom (finishCandidate start) scanned := by
    rw [outerIterationSteps, natRun_add, natRun_add]
    exact run_finishCandidate rom containing start hbound hcode scanned hip hia
  dsimp only
  rw [hbody]
  refine ⟨?_, ?_, ?_, ?_, hc.1, hc.2.trans hia⟩
  · rw [hheap]
    simp
  · rw [hheap]
    simpa [show cardAddress base index ≠ base + 1 by unfold cardAddress; omega,
      show cardAddress base index ≠ keepAddress base (full.length + q + 1) index by
        unfold cardAddress keepAddress; omega] using hscanCard
  · rw [hheap]
    simp [keepAddress, show base + 4 + (full.length + q + 1) + index ≠ base + 1 by omega]
  · intro address haddr h1 h2 h3 hcaddr hkaddr
    rw [hheap]
    simp only [Function.update_of_ne h1, Function.update_of_ne hkaddr]
    exact (hiframe address haddr h2 h3).trans (hsframe address haddr h2 h3 hcaddr)

def OutsideWorkspace (base count address : Nat) : Prop :=
  8 ≤ address ∧ address ≠ base + 1 ∧ address ≠ base + 2 ∧ address ≠ base + 3 ∧
    (address < base + 4 ∨ base + 4 + 2 * count ≤ address)

def outerScanSteps (N q count : Nat) : Nat := ∑ index ∈ Finset.range count, outerIterationSteps N q index

theorem outerScanSteps_succ (N q count : Nat) :
    outerScanSteps N q (count + 1) = outerScanSteps N q count + outerIterationSteps N q count :=
  Finset.sum_range_succ _ _

theorem outer_scan_partial (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 398 ≤ containing.length)
    (hcode : ∀ position < 398, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base : Nat) (hlarge : 16 ≤ base) (state : NatState) (hbase : state.heap 8 = base)
    (hcount : state.heap base = full.length + q + 1) (hindex : state.heap (base + 1) = 0)
    (hpc : state.pc = 5 * (start + 6)) (hactive : state.halted = false)
    (count : Nat) (hwithin : count ≤ full.length + q + 1) :
    let result := natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q count) state
    result.heap (base + 1) = count ∧
      (∀ index < count, result.heap (cardAddress base index) =
        ((RawCandidateOrder.candidateSupports q full).getD index ∅).card ∧
        result.heap (keepAddress base (full.length + q + 1) index) = bit (RawCandidateOrder.keepCandidate q full index)) ∧
      (∀ address, OutsideWorkspace base (full.length + q + 1) address → result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 6) ∧ result.halted = false := by
  revert hwithin
  induction count with
  | zero =>
    intro _
    simpa only [outerScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show state.heap (base + 1) = 0 ∧
        (∀ index < 0, state.heap (cardAddress base index) =
          ((RawCandidateOrder.candidateSupports q full).getD index ∅).card ∧
          state.heap (keepAddress base (full.length + q + 1) index) = bit (RawCandidateOrder.keepCandidate q full index)) ∧
        (∀ address, OutsideWorkspace base (full.length + q + 1) address → state.heap address = state.heap address) ∧
        state.pc = 5 * (start + 6) ∧ state.halted = false from
          ⟨hindex, fun _ hi => by omega, fun _ _ => rfl, hpc, hactive⟩)
  | succ count ih =>
    intro hwithin
    rcases ih (by omega) with ⟨hi, hprefix, hframe, hp, ha⟩
    let previous := natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q count) state
    have hb' : previous.heap 8 = base :=
      (hframe 8 ⟨le_rfl, by omega, by omega, by omega, Or.inl (by omega)⟩).trans hbase
    have hm' : previous.heap base = full.length + q + 1 :=
      (hframe base ⟨by omega, by omega, by omega, by omega, Or.inl (by omega)⟩).trans hcount
    have hs := outer_iteration q full containing start hbound hcode base count hlarge (by omega)
      previous hb' hm' hi hp ha
    dsimp only at hs
    rcases hs with ⟨hsi, hsc, hsk, hsframe, hsp, hsa⟩
    have hrun : natRun (rawIncidenceROM q full) containing (outerScanSteps full.length q (count + 1)) state =
        natRun (rawIncidenceROM q full) containing (outerIterationSteps full.length q count) previous := by
      rw [outerScanSteps_succ, natRun_add]
    dsimp only
    rw [hrun]
    refine ⟨hsi, ?_, ?_, hsp, hsa⟩
    · intro index hindex'
      by_cases heq : index = count
      · subst index
        exact ⟨hsc, hsk⟩
      · have hless : index < count := by omega
        obtain ⟨hpcard, hpkeep⟩ := hprefix index hless
        constructor
        · exact (hsframe (cardAddress base index) (by unfold cardAddress; omega)
            (by unfold cardAddress; omega) (by unfold cardAddress; omega) (by unfold cardAddress; omega)
            (by unfold cardAddress; omega) (by unfold cardAddress keepAddress; omega)).trans hpcard
        · exact (hsframe (keepAddress base (full.length + q + 1) index) (by unfold keepAddress; omega)
            (by unfold keepAddress; omega) (by unfold keepAddress; omega) (by unfold keepAddress; omega)
            (by unfold cardAddress keepAddress; omega) (by unfold keepAddress; omega)).trans hpkeep
    · intro address hout
      rcases hout with ⟨haddr, h1, h2, h3, hregion⟩
      exact (hsframe address haddr h1 h2 h3
        (by unfold cardAddress; rcases hregion with hregion | hregion <;> omega)
        (by unfold keepAddress; rcases hregion with hregion | hregion <;> omega)).trans
          (hframe address ⟨haddr, h1, h2, h3, hregion⟩)

def totalSteps (N q : Nat) : Nat := 6 + outerScanSteps N q (N + q + 1) + 13

/-- The complete actual double loop materializes every raw candidate's
cardinality and original last-occurrence keep bit.  The input workspace
header is a caller-established runtime invariant, not a supplied answer. -/
theorem retention (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 398 ≤ containing.length)
    (hcode : ∀ position < 398, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (base : Nat) (hlarge : 16 ≤ base) (state : NatState)
    (hbase : state.heap 8 = base) (hcount : state.heap base = full.length + q + 1)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps full.length q) state
    result.heap 8 = base ∧ result.heap base = full.length + q + 1 ∧
      result.heap (base + 1) = full.length + q + 1 ∧
      (∀ index < full.length + q + 1,
        result.heap (cardAddress base index) = ((RawCandidateOrder.candidateSupports q full).getD index ∅).card ∧
        result.heap (keepAddress base (full.length + q + 1) index) = bit (RawCandidateOrder.keepCandidate q full index)) ∧
      (∀ address, OutsideWorkspace base (full.length + q + 1) address → result.heap address = state.heap address) ∧
      result.pc = 5 * (start + 398) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom (setWorkspace 1 0) state
  have hinitHeap : initialized.heap = Function.update state.heap (base + 1) 0 := by
    simpa only [hbase] using setWorkspace_heap rom 1 0 state
  have hiBase : initialized.heap 8 = base := by
    rw [hinitHeap]
    simpa [show 8 ≠ base + 1 by omega] using hbase
  have hiCount : initialized.heap base = full.length + q + 1 := by
    rw [hinitHeap]
    simpa using hcount
  have hiIndex : initialized.heap (base + 1) = 0 := by rw [hinitHeap]; simp
  have hiPc : initialized.pc = 5 * (start + 6) := by
    rw [show initialized = runOps rom (setWorkspace 1 0) state from rfl,
      runOps_pc rom (setWorkspace 1 0) state (by simp [setWorkspace, storeWorkspace, loadCell, NoJump]),
      setWorkspace_length, hpc]
    omega
  have hiActive : initialized.halted = false := by dsimp [initialized]; rw [runOps_halted, hactive]
  have hs := outer_scan_partial q full containing start hbound hcode base hlarge initialized
    hiBase hiCount hiIndex hiPc hiActive (full.length + q + 1) le_rfl
  dsimp only at hs
  rcases hs with ⟨hsIndex, hsArrays, hsFrame, hsPc, hsActive⟩
  let previous := natRun rom containing (outerScanSteps full.length q (full.length + q + 1)) initialized
  have hpBase : previous.heap 8 = base :=
    (hsFrame 8 ⟨le_rfl, by omega, by omega, by omega, Or.inl (by omega)⟩).trans hiBase
  have hpCount : previous.heap base = full.length + q + 1 :=
    (hsFrame base ⟨by omega, by omega, by omega, by omega, Or.inl (by omega)⟩).trans hiCount
  have ht := testWorkspace_values rom 1 (start + 398) previous
  have hbody : natRun rom containing (totalSteps full.length q) state =
      runOps rom (testWorkspace 1 (start + 398)) previous := by
    rw [show totalSteps full.length q = 6 + (outerScanSteps full.length q (full.length + q + 1) + 13) by
      unfold totalSteps; omega, natRun_add, run_init rom containing start hbound hcode state hpc hactive]
    rw [natRun_add]
    exact run_outerTest rom containing start hbound hcode previous hsPc hsActive
  dsimp only
  rw [hbody]
  refine ⟨(congrFun ht.1 8).trans hpBase, (congrFun ht.1 base).trans hpCount,
    (congrFun ht.1 (base + 1)).trans hsIndex, ?_, ?_, ?_, ht.2.2.trans hsActive⟩
  · intro index hi
    obtain ⟨hc, hk⟩ := hsArrays index hi
    exact ⟨(congrFun ht.1 _).trans hc, (congrFun ht.1 _).trans hk⟩
  · intro address hout
    rw [(congrFun ht.1 address), hsFrame address hout, hinitHeap]
    exact Function.update_of_ne hout.2.1 _ _
  · have hp := ht.2.1
    rw [hpBase, hpCount, show previous.heap (base + 1) = full.length + q + 1 from hsIndex,
      Nat.sub_self] at hp
    exact hp

theorem outerIterationSteps_le (N q index : Nat) (hi : index < N + q + 1) :
    outerIterationSteps N q index ≤ (N + q + 1) * (174 * q + 201) := by
  let M := N + q + 1
  have hm : 1 ≤ M := by dsimp [M]; omega
  have hp := RawCandidatePairScan.totalSteps_le N index 0 q
  have hs := innerScanSteps_le N q index (index + 1) (N + q + 1 - (index + 1))
  have hcnt : N + q + 1 - (index + 1) ≤ M := by dsimp [M]; omega
  have hs' : innerScanSteps N q index (index + 1) (N + q + 1 - (index + 1)) ≤ M * (87 * q + 82) :=
    hs.trans (Nat.mul_le_mul_right (87 * q + 82) hcnt)
  have hscaled : 87 * q + 119 ≤ M * (87 * q + 119) := by nlinarith
  unfold outerIterationSteps cardPhaseSteps innerCompleteSteps
  change _ ≤ M * (174 * q + 201)
  nlinarith

theorem totalSteps_le (N q : Nat) : totalSteps N q ≤ 512 * (N + q + 1) ^ 2 * (q + 1) := by
  let M := N + q + 1
  have hm : 1 ≤ M := by dsimp [M]; omega
  have hsum : outerScanSteps N q M ≤ M * (M * (174 * q + 201)) := by
    unfold outerScanSteps
    calc
      _ ≤ ∑ _index ∈ Finset.range M, (M * (174 * q + 201)) :=
        Finset.sum_le_sum (fun index hi => outerIterationSteps_le N q index (Finset.mem_range.mp hi))
      _ = _ := by simp [Nat.mul_comm]
  have hMM : 1 ≤ M * M := by nlinarith
  have hterm : 0 ≤ M * M * q := Nat.zero_le _
  unfold totalSteps
  change 6 + outerScanSteps N q M + 13 ≤ 512 * M ^ 2 * (q + 1)
  nlinarith

end PaperProofs.Structure.LaminarTree.RawCandidateRetentionRAM
