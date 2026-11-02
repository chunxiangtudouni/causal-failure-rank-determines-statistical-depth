module

public import PaperProofs.Structure.RawCandidateSerializedReady
public import PaperProofs.Structure.RawCandidateChildrenLayout
import Mathlib.Tactic.Linarith

/-! Fixed, relocatable runtime parent/child serialization.  Cache accesses
recompute the workspace base from the readonly raw header.  Cell 8 is output
data and is never interpreted as a pointer by this phase. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateWorkspaceInit
  RawCandidateSerializedInputRAM RawCandidateSerializedReady

def parentAddress (N q child : Nat) : Nat :=
  workspaceBase N q + 5 + 4 * candidateCount N q + child

def flatAddress (N q : Nat) : Nat := workspaceBase N q + 5 + 5 * candidateCount N q

def loadParent (counter : Nat) : List PackingOp :=
  loadCache .old counter ++ RawCandidateWorkspaceBaseRAM.program ++
    [.base (.base (.constant .index 4)), .arithmetic .multiply .index .total .index,
      .base (.base (.add .address .address .index)), .base (.base (.constant .index 5)),
      .base (.base (.add .address .address .index)), .base (.base (.add .address .address .old)),
      .base (.base (.loadHeap .value .address))]

def loadFlat (target : Register) : List PackingOp :=
  RawCandidateWorkspaceBaseRAM.program ++
    [.base (.base (.constant .index 5)), .arithmetic .multiply .index .total .index,
      .base (.base (.add .address .address .index)), .base (.base (.constant .index 5)),
      .base (.base (.add .address .address .index)), .base (.base (.loadHeap target .address))]

def storeFlat : List PackingOp :=
  RawCandidateWorkspaceBaseRAM.program ++
    [.base (.base (.constant .index 5)), .arithmetic .multiply .index .total .index,
      .base (.base (.add .address .address .index)), .base (.base (.constant .index 5)),
      .base (.base (.add .address .address .index)), .base (.base (.storeHeap .address .value))]

def setFlat : List PackingOp := [.base (.base (.constant .value 0))] ++ storeFlat

def incrementFlat : List PackingOp :=
  loadFlat .value ++ [.base (.base (.constant .index 1)), .base (.base (.add .value .value .index))] ++ storeFlat

def initBlock : List PackingOp := setCache 1 0 ++ setFlat

def writeParent : List PackingOp :=
  loadParent 1 ++ loadCell .fresh 0 ++
    [.base (.base (.constant .address 3)), .base (.base (.add .address .address .fresh)),
      .base (.base (.add .address .address .old)), .base (.base (.storeHeap .address .value))]

def initRow : List PackingOp := writeParent ++ setCache 3 0 ++ setCache 2 0

def matchLead (start : Nat) : List PackingOp :=
  loadParent 2 ++ loadCache .old 1 ++
    [.base (.base (.constant .index 1)), .base (.base (.add .old .old .index)),
      .base (.subtract .flag .value .old), .base (.subtract .total .old .value),
      .base (.base (.add .flag .flag .total)), .base (.base (.constant .index (5 * (start + 206))))]

def matchTest (start : Nat) : List PackingOp := matchLead start ++ [.jumpIfZero .flag .index]

def writeChild : List PackingOp :=
  loadCache .fresh 2 ++ loadFlat .value ++ loadCell .old 0 ++ loadCell .total 1 ++
    [.base (.base (.add .address .old .total)), .base (.base (.constant .index 3)),
      .base (.base (.add .address .address .index)), .base (.base (.add .address .address .value)),
      .base (.base (.storeHeap .address .fresh))]

def matched : List PackingOp := writeChild ++ incrementCache 3 ++ incrementFlat

def innerLead (start : Nat) : List PackingOp := incrementCache 2 ++ (jumpTo (start + 127)).take 2

def innerTail (start : Nat) : List PackingOp := innerLead start ++ [.jumpIfZero .flag .index]

def writeDegree : List PackingOp :=
  loadCache .value 3 ++ loadCache .old 1 ++ loadCell .fresh 5 ++ loadCell .total 0 ++
    [.base (.base (.add .address .total .fresh)), .base (.base (.constant .index 3)),
      .base (.base (.add .address .address .index)), .base (.base (.add .address .address .old)),
      .base (.base (.storeHeap .address .value))]

def outerLead (start : Nat) : List PackingOp := writeDegree ++ incrementCache 1 ++ (jumpTo (start + 35)).take 2

def outerTail (start : Nat) : List PackingOp := outerLead start ++ [.jumpIfZero .flag .index]

def programAt (start : Nat) : List PackingOp :=
  initBlock ++ boundedTest 1 5 (start + 427) ++ initRow ++ boundedTest 2 5 (start + 353) ++
    matchTest start ++ jumpTo (start + 318) ++ matched ++ innerTail start ++ outerTail start

theorem loadParent_length (counter : Nat) : (loadParent counter).length = 34 := by
  simp only [loadParent, loadCache_length, RawCandidateWorkspaceBaseRAM.program_length,
    List.length_append, List.length_cons, List.length_nil]

theorem loadFlat_length (target : Register) : (loadFlat target).length = 18 := by
  simp only [loadFlat, RawCandidateWorkspaceBaseRAM.program_length,
    List.length_append, List.length_cons, List.length_nil]

theorem storeFlat_length : storeFlat.length = 18 := by
  simp only [storeFlat, RawCandidateWorkspaceBaseRAM.program_length,
    List.length_append, List.length_cons, List.length_nil]

theorem setFlat_length : setFlat.length = 19 := by
  simp only [setFlat, storeFlat_length, List.length_append, List.length_cons, List.length_nil]

theorem incrementFlat_length : incrementFlat.length = 38 := by
  simp only [incrementFlat, loadFlat_length, storeFlat_length,
    List.length_append, List.length_cons, List.length_nil]

theorem initBlock_length : initBlock.length = 35 := by
  simp only [initBlock, setCache_length, setFlat_length, List.length_append]

theorem writeParent_length : writeParent.length = 40 := by
  simp only [writeParent, loadParent_length, loadCell, List.length_append, List.length_cons, List.length_nil]

theorem initRow_length : initRow.length = 72 := by
  simp only [initRow, writeParent_length, setCache_length, List.length_append]

theorem matchLead_length (start : Nat) : (matchLead start).length = 55 := by
  simp only [matchLead, loadParent_length, loadCache_length, List.length_append, List.length_cons, List.length_nil]

theorem matchTest_length (start : Nat) : (matchTest start).length = 56 := by
  simp only [matchTest, matchLead_length, List.length_append, List.length_cons, List.length_nil]

theorem writeChild_length : writeChild.length = 42 := by
  simp only [writeChild, loadCache_length, loadFlat_length, loadCell,
    List.length_append, List.length_cons, List.length_nil]

theorem matched_length : matched.length = 112 := by
  simp only [matched, writeChild_length, incrementCache_length, incrementFlat_length, List.length_append]

theorem innerLead_length (start : Nat) : (innerLead start).length = 34 := by
  simp only [innerLead, incrementCache_length, jumpTo, List.take_succ_cons, List.take_zero,
    List.length_append, List.length_cons, List.length_nil]

theorem innerTail_length (start : Nat) : (innerTail start).length = 35 := by
  simp only [innerTail, innerLead_length, List.length_append, List.length_cons, List.length_nil]

theorem writeDegree_length : writeDegree.length = 39 := by
  simp only [writeDegree, loadCache_length, loadCell, List.length_append, List.length_cons, List.length_nil]

theorem outerLead_length (start : Nat) : (outerLead start).length = 73 := by
  simp only [outerLead, writeDegree_length, incrementCache_length, jumpTo, List.take_succ_cons,
    List.take_zero, List.length_append, List.length_cons, List.length_nil]

theorem outerTail_length (start : Nat) : (outerTail start).length = 74 := by
  simp only [outerTail, outerLead_length, List.length_append, List.length_cons, List.length_nil]

theorem programAt_length (start : Nat) : (programAt start).length = 427 := by
  simp only [programAt, initBlock_length, boundedTest_length, initRow_length, matchTest_length,
    jumpTo, matched_length, innerTail_length, outerTail_length,
    List.length_append, List.length_cons, List.length_nil]

private theorem state_ext {left right : NatState}
    (hr : left.register = right.register) (hh : left.heap = right.heap)
    (hp : left.pc = right.pc) (ha : left.halted = right.halted) : left = right := by
  cases left
  cases right
  cases hr
  cases hh
  cases hp
  cases ha
  rfl

def parentLoaded (N q counter : Nat) (state : NatState) : NatState :=
  { state with
    register := fun reg => match reg with
      | .old => state.heap (workspaceBase N q + counter)
      | .fresh => state.register .fresh
      | .value => state.heap (parentAddress N q (state.heap (workspaceBase N q + counter)))
      | .total => candidateCount N q
      | .flag => q
      | .address => parentAddress N q (state.heap (workspaceBase N q + counter))
      | .index => 5
    pc := state.pc + 170 }

theorem loadParent_runOps (q : Nat) (full : List (Finset (Fin q))) (counter : Nat) (state : NatState) :
    runOps (rawIncidenceROM q full) (loadParent counter) state = parentLoaded full.length q counter state := by
  simp only [loadParent, runOps_append, loadCache_runOps, base_runOps]
  apply state_ext
  · funext reg
    cases reg <;> simp [parentLoaded, parentAddress, loaded, recovered, runOps, natExecuteOp,
      natArithmetic, Op.execute, Instruction.execute, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  · simp [parentLoaded, loaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [parentLoaded, loaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [parentLoaded, loaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]

def flatLoaded (N q : Nat) (target : Register) (state : NatState) : NatState :=
  { recovered N q state with
    register := Function.update
      (Function.update (Function.update (recovered N q state).register .index 5)
        .address (flatAddress N q)) target (state.heap (flatAddress N q))
    pc := state.pc + 90 }

theorem loadFlat_runOps (q : Nat) (full : List (Finset (Fin q))) (target : Register) (state : NatState) :
    runOps (rawIncidenceROM q full) (loadFlat target) state = flatLoaded full.length q target state := by
  rw [loadFlat, runOps_append, base_runOps]
  apply state_ext
  · funext reg
    cases reg <;> cases target <;> simp [flatLoaded, flatAddress, recovered, runOps, natExecuteOp,
      natArithmetic, Op.execute, Instruction.execute, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  · simp [flatLoaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [flatLoaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [flatLoaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]

def flatStored (N q : Nat) (state : NatState) : NatState :=
  { recovered N q state with
    register := Function.update
      (Function.update (recovered N q state).register .index 5) .address (flatAddress N q)
    heap := Function.update state.heap (flatAddress N q) (state.register .value)
    pc := state.pc + 90 }

theorem storeFlat_runOps (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    runOps (rawIncidenceROM q full) storeFlat state = flatStored full.length q state := by
  rw [storeFlat, runOps_append, base_runOps]
  apply state_ext
  · funext reg
    cases reg <;> simp [flatStored, flatAddress, recovered, runOps, natExecuteOp,
      natArithmetic, Op.execute, Instruction.execute, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  · simp [flatStored, flatAddress, recovered, runOps, natExecuteOp, natArithmetic, Op.execute,
      Instruction.execute, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  · simp [flatStored, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [flatStored, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem incrementFlat_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    (runOps (rawIncidenceROM q full) incrementFlat state).heap =
      Function.update state.heap (flatAddress full.length q) (state.heap (flatAddress full.length q) + 1) := by
  simp only [incrementFlat, runOps_append, loadFlat_runOps, storeFlat_runOps]
  simp [flatLoaded, flatStored, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem setFlat_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    (runOps (rawIncidenceROM q full) setFlat state).heap = Function.update state.heap (flatAddress full.length q) 0 := by
  simp only [setFlat, runOps_append, storeFlat_runOps]
  simp [flatStored, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem initBlock_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    (runOps (rawIncidenceROM q full) initBlock state).heap =
      Function.update (Function.update state.heap (workspaceBase full.length q + 1) 0) (flatAddress full.length q) 0 := by
  simp only [initBlock, runOps_append, setFlat_heap, setCache_heap]

theorem writeParent_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    (runOps (rawIncidenceROM q full) writeParent state).heap =
      Function.update state.heap (3 + state.heap 0 + state.heap (workspaceBase full.length q + 1))
        (state.heap (parentAddress full.length q (state.heap (workspaceBase full.length q + 1)))) := by
  simp only [writeParent, runOps_append, loadParent_runOps]
  simp [parentLoaded, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
    Nat.add_comm, Nat.add_left_comm]

theorem initRow_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    (runOps (rawIncidenceROM q full) initRow state).heap =
      Function.update (Function.update
        (Function.update state.heap (3 + state.heap 0 + state.heap (workspaceBase full.length q + 1))
          (state.heap (parentAddress full.length q (state.heap (workspaceBase full.length q + 1)))))
        (workspaceBase full.length q + 3) 0) (workspaceBase full.length q + 2) 0 := by
  simp only [initRow, runOps_append, setCache_heap, writeParent_heap]

theorem matchTest_values (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState) :
    let result := runOps (rawIncidenceROM q full) (matchTest start) state
    result.heap = state.heap ∧ result.halted = state.halted ∧
      result.pc = if state.heap (parentAddress full.length q (state.heap (workspaceBase full.length q + 2))) =
        state.heap (workspaceBase full.length q + 1) + 1 then 5 * (start + 206) else state.pc + 280 := by
  simp only [matchTest, matchLead, runOps_append, loadParent_runOps, loadCache_runOps]
  simp [parentLoaded, loaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  split <;> split <;> omega

theorem writeChild_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    (runOps (rawIncidenceROM q full) writeChild state).heap =
      Function.update state.heap (3 + state.heap 0 + state.heap 1 + state.heap (flatAddress full.length q))
        (state.heap (workspaceBase full.length q + 2)) := by
  simp only [writeChild, runOps_append, loadCache_runOps, loadFlat_runOps]
  simp [loaded, flatLoaded, recovered, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem writeDegree_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    (runOps (rawIncidenceROM q full) writeDegree state).heap =
      Function.update state.heap (3 + state.heap 0 + state.heap 5 + state.heap (workspaceBase full.length q + 1))
        (state.heap (workspaceBase full.length q + 3)) := by
  simp only [writeDegree, runOps_append, loadCache_runOps]
  simp [loaded, recovered, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

def paddingOp : PackingOp := RawCandidateSerializedInputRAM.paddingOp

private theorem getD_middle (left middle right : List PackingOp) (position : Nat)
    (hp : position < middle.length) :
    (left ++ middle ++ right).getD (left.length + position) paddingOp = middle.getD position paddingOp := by
  rw [List.getD_append (left ++ middle) right paddingOp _ (by simp; omega),
    List.getD_append_right left middle paddingOp _ (by omega), Nat.add_sub_cancel_left]

section Containing

variable (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
  (hbound : start + 427 ≤ containing.length)
  (hcode : ∀ position < 427, containing.getD (start + position) paddingOp =
    (programAt start).getD position paddingOp)

include hbound hcode

private theorem containing_slice (leading block suffix : List PackingOp) (offset : Nat)
    (hlayout : programAt start = leading ++ block ++ suffix) (hprefix : leading.length = offset) :
    start + offset + block.length ≤ containing.length ∧
      ∀ position < block.length, containing.getD ((start + offset) + position) paddingOp = block.getD position paddingOp := by
  have hspan : offset + block.length ≤ 427 := by
    have hl := congrArg List.length hlayout
    simp only [programAt_length, List.length_append, hprefix] at hl
    omega
  refine ⟨by omega, ?_⟩
  intro position hp
  have hh := hcode (offset + position) (by omega)
  have hm := getD_middle leading block suffix position hp
  rw [← hlayout, hprefix] at hm
  simpa only [Nat.add_assoc] using hh.trans hm

private theorem run_straight_layout (leading block suffix : List PackingOp) (offset : Nat)
    (hlayout : programAt start = leading ++ block ++ suffix) (hprefix : leading.length = offset)
    (hstraight : ∀ op ∈ block, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing block.length state = runOps rom block state := by
  have hs := containing_slice containing start hbound hcode leading block suffix offset hlayout hprefix
  apply natRun_of_straight_segment rom containing block (start + offset) (by omega) ?_ hstraight state hpc hactive
  intro position hp
  have hh := hs.2 position hp
  rw [List.getD_eq_getElem containing paddingOp (by omega), List.getD_eq_getElem block paddingOp hp] at hh
  exact hh

private theorem run_branch_layout (leading lead suffix : List PackingOp) (last : PackingOp) (offset : Nat)
    (hlayout : programAt start = leading ++ (lead ++ [last]) ++ suffix) (hprefix : leading.length = offset)
    (hstraight : ∀ op ∈ lead, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (hactive : state.halted = false) :
    natRun rom containing (lead.length + 1) state = runOps rom (lead ++ [last]) state := by
  have hs := containing_slice containing start hbound hcode leading (lead ++ [last]) suffix offset hlayout hprefix
  have hsize : start + offset + (lead.length + 1) ≤ containing.length := by
    simpa only [List.length_append, List.length_cons, List.length_nil] using hs.1
  rw [runOps_append, runOps]
  apply natRun_of_segment_last rom containing lead last (start + offset) (by omega) ?_ ?_ hstraight state hpc hactive
  · intro position hp
    have hh := hs.2 position (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    rw [List.getD_append lead [last] paddingOp position hp,
      List.getD_eq_getElem containing paddingOp (by omega), List.getD_eq_getElem lead paddingOp hp] at hh
    exact hh
  · have hh := hs.2 lead.length (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    rw [List.getD_append_right lead [last] paddingOp lead.length le_rfl, Nat.sub_self,
      List.getD_cons_zero, List.getD_eq_getElem containing paddingOp (by omega)] at hh
    exact hh

theorem run_initBlock (state : NatState) (hpc : state.pc = 5 * (start + 0)) (hactive : state.halted = false) :
    natRun rom containing 35 state = runOps rom (initBlock) state := by
  let leading := ([] : List PackingOp)
  let suffix := boundedTest 1 5 (start + 427) ++ initRow ++ boundedTest 2 5 (start + 353) ++ matchTest start ++ jumpTo (start + 318) ++ matched ++ innerTail start ++ outerTail start
  have hlayout : programAt start = leading ++ (initBlock) ++ suffix := by
    simp only [programAt, leading, suffix, List.nil_append,  List.append_assoc]
  have hprefix : leading.length = 0 := by
    simp only [leading,           List.length_nil, List.length_nil]
  have hh := run_straight_layout rom containing start hbound hcode leading (initBlock) suffix 0
    hlayout hprefix (by dsimp [initBlock, setCache, setFlat, storeFlat,           storeCache, RawCandidateWorkspaceBaseRAM.program,  NoJump]; simp) state hpc hactive
  simpa only [initBlock_length] using hh

theorem run_outerTest (state : NatState) (hpc : state.pc = 5 * (start + 35)) (hactive : state.halted = false) :
    natRun rom containing 20 state = runOps rom (boundedTest 1 5 (start + 427)) state := by
  let leading := initBlock
  let suffix := initRow ++ boundedTest 2 5 (start + 353) ++ matchTest start ++ jumpTo (start + 318) ++ matched ++ innerTail start ++ outerTail start
  let lead := loadCache .total 1 ++ loadCell .old 5 ++
    [.base (.subtract .flag .old .total), .base (.base (.constant .index (5 * (start + 427))))]
  have hlead : lead ++ [.jumpIfZero .flag .index] = (boundedTest 1 5 (start + 427)) := by
    simp only [lead, boundedTest, List.append_assoc, List.cons_append, List.nil_append]
  have hlength : lead.length = 19 := by
    simp only [lead, loadCache_length, loadCell,   
         List.length_append, List.length_cons, List.length_nil]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix,   List.append_assoc]
  have hprefix : leading.length = 35 := by
    simp only [leading, initBlock_length]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix (.jumpIfZero .flag .index) 35
    hlayout hprefix (by dsimp [lead,     
                    loadCache,  RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]; simp) state hpc hactive
  simpa only [hlength, hlead] using hh

theorem run_initRow (state : NatState) (hpc : state.pc = 5 * (start + 55)) (hactive : state.halted = false) :
    natRun rom containing 72 state = runOps rom (initRow) state := by
  let leading := initBlock ++ boundedTest 1 5 (start + 427)
  let suffix := boundedTest 2 5 (start + 353) ++ matchTest start ++ jumpTo (start + 318) ++ matched ++ innerTail start ++ outerTail start
  have hlayout : programAt start = leading ++ (initRow) ++ suffix := by
    simp only [programAt, leading, suffix,   List.append_assoc]
  have hprefix : leading.length = 55 := by
    simp only [leading, initBlock_length, boundedTest_length,       List.length_append]
  have hh := run_straight_layout rom containing start hbound hcode leading (initRow) suffix 55
    hlayout hprefix (by dsimp [ setCache,     initRow, writeParent, loadParent,     loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]; simp) state hpc hactive
  simpa only [initRow_length] using hh

theorem run_innerTest (state : NatState) (hpc : state.pc = 5 * (start + 127)) (hactive : state.halted = false) :
    natRun rom containing 20 state = runOps rom (boundedTest 2 5 (start + 353)) state := by
  let leading := initBlock ++ boundedTest 1 5 (start + 427) ++ initRow
  let suffix := matchTest start ++ jumpTo (start + 318) ++ matched ++ innerTail start ++ outerTail start
  let lead := loadCache .total 2 ++ loadCell .old 5 ++
    [.base (.subtract .flag .old .total), .base (.base (.constant .index (5 * (start + 353))))]
  have hlead : lead ++ [.jumpIfZero .flag .index] = (boundedTest 2 5 (start + 353)) := by
    simp only [lead, boundedTest, List.append_assoc, List.cons_append, List.nil_append]
  have hlength : lead.length = 19 := by
    simp only [lead, loadCache_length, loadCell,   
         List.length_append, List.length_cons, List.length_nil]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix,   List.append_assoc]
  have hprefix : leading.length = 127 := by
    simp only [leading, initBlock_length, boundedTest_length, initRow_length,      List.length_append]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix (.jumpIfZero .flag .index) 127
    hlayout hprefix (by dsimp [lead, matchLead, innerLead, outerLead, jumpTo, List.take_succ_cons,
      List.take_zero, initBlock, setCache, setFlat, storeFlat, loadFlat, incrementFlat, initRow, writeParent, loadParent, matched, writeChild, writeDegree, incrementCache, loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]; simp) state hpc hactive
  simpa only [hlength, hlead] using hh

theorem run_matchTest (state : NatState) (hpc : state.pc = 5 * (start + 147)) (hactive : state.halted = false) :
    natRun rom containing 56 state = runOps rom (matchTest start) state := by
  let leading := initBlock ++ boundedTest 1 5 (start + 427) ++ initRow ++ boundedTest 2 5 (start + 353)
  let suffix := jumpTo (start + 318) ++ matched ++ innerTail start ++ outerTail start
  let lead := matchLead start
  have hlead : lead ++ [.jumpIfZero .flag .index] = (matchTest start) := by
    simp only [lead, matchTest]
  have hlength : lead.length = 55 := by
    simp only [lead,   matchLead_length]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix,   List.append_assoc]
  have hprefix : leading.length = 147 := by
    simp only [leading, initBlock_length, boundedTest_length, initRow_length,      List.length_append]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix (.jumpIfZero .flag .index) 147
    hlayout hprefix (by dsimp [lead, matchLead, innerLead, outerLead, jumpTo, List.take_succ_cons,
      List.take_zero, initBlock, setCache, setFlat, storeFlat, loadFlat, incrementFlat, initRow, writeParent, loadParent, matched, writeChild, writeDegree, incrementCache, loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]; simp) state hpc hactive
  simpa only [hlength, hlead] using hh

theorem run_skipMatch (state : NatState) (hpc : state.pc = 5 * (start + 203)) (hactive : state.halted = false) :
    natRun rom containing 3 state = runOps rom (jumpTo (start + 318)) state := by
  let leading := initBlock ++ boundedTest 1 5 (start + 427) ++ initRow ++ boundedTest 2 5 (start + 353) ++ matchTest start
  let suffix := matched ++ innerTail start ++ outerTail start
  let lead := (jumpTo (start + 318)).take 2
  have hlead : lead ++ [.jumpIfZero .flag .index] = (jumpTo (start + 318)) := by
    simp only [lead, jumpTo, List.take_succ_cons, List.take_zero,  List.cons_append, List.nil_append]
  have hlength : lead.length = 2 := by
    simp only [lead,     
      jumpTo, List.take_succ_cons, List.take_zero,  List.length_cons, List.length_nil]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix,   List.append_assoc]
  have hprefix : leading.length = 203 := by
    simp only [leading, initBlock_length, boundedTest_length, initRow_length, matchTest_length,     List.length_append]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix (.jumpIfZero .flag .index) 203
    hlayout hprefix (by dsimp [lead, matchLead, innerLead, outerLead, jumpTo, List.take_succ_cons,
      List.take_zero, initBlock, setCache, setFlat, storeFlat, loadFlat, incrementFlat, initRow, writeParent, loadParent, matched, writeChild, writeDegree, incrementCache, loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]; simp) state hpc hactive
  simpa only [hlength, hlead] using hh

theorem run_matched (state : NatState) (hpc : state.pc = 5 * (start + 206)) (hactive : state.halted = false) :
    natRun rom containing 112 state = runOps rom (matched) state := by
  let leading := initBlock ++ boundedTest 1 5 (start + 427) ++ initRow ++ boundedTest 2 5 (start + 353) ++ matchTest start ++ jumpTo (start + 318)
  let suffix := innerTail start ++ outerTail start
  have hlayout : programAt start = leading ++ (matched) ++ suffix := by
    simp only [programAt, leading, suffix,   List.append_assoc]
  have hprefix : leading.length = 206 := by
    simp only [leading, initBlock_length, boundedTest_length, initRow_length, matchTest_length, jumpTo,    List.length_append, List.length_cons, List.length_nil, List.length_nil]
  have hh := run_straight_layout rom containing start hbound hcode leading (matched) suffix 206
    hlayout hprefix (by dsimp [initBlock, setCache, setFlat, storeFlat, loadFlat, incrementFlat, initRow, writeParent, loadParent, matched, writeChild, writeDegree, incrementCache, loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]; simp) state hpc hactive
  simpa only [matched_length] using hh

theorem run_innerTail (state : NatState) (hpc : state.pc = 5 * (start + 318)) (hactive : state.halted = false) :
    natRun rom containing 35 state = runOps rom (innerTail start) state := by
  let leading := initBlock ++ boundedTest 1 5 (start + 427) ++ initRow ++ boundedTest 2 5 (start + 353) ++ matchTest start ++ jumpTo (start + 318) ++ matched
  let suffix := outerTail start
  let lead := innerLead start
  have hlead : lead ++ [.jumpIfZero .flag .index] = (innerTail start) := by
    simp only [lead, innerTail]
  have hlength : lead.length = 34 := by
    simp only [lead,    innerLead_length]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix,   List.append_assoc]
  have hprefix : leading.length = 318 := by
    simp only [leading, initBlock_length, boundedTest_length, initRow_length, matchTest_length, jumpTo, matched_length,   List.length_append, List.length_cons, List.length_nil]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix (.jumpIfZero .flag .index) 318
    hlayout hprefix (by dsimp [lead, matchLead, innerLead, outerLead, jumpTo, List.take_succ_cons,
      List.take_zero, initBlock, setCache, setFlat, storeFlat, loadFlat, incrementFlat, initRow, writeParent, loadParent, matched, writeChild, writeDegree, incrementCache, loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]; simp) state hpc hactive
  simpa only [hlength, hlead] using hh

theorem run_outerTail (state : NatState) (hpc : state.pc = 5 * (start + 353)) (hactive : state.halted = false) :
    natRun rom containing 74 state = runOps rom (outerTail start) state := by
  let leading := initBlock ++ boundedTest 1 5 (start + 427) ++ initRow ++ boundedTest 2 5 (start + 353) ++ matchTest start ++ jumpTo (start + 318) ++ matched ++ innerTail start
  let suffix := ([] : List PackingOp)
  let lead := outerLead start
  have hlead : lead ++ [.jumpIfZero .flag .index] = (outerTail start) := by
    simp only [lead, outerTail]
  have hlength : lead.length = 73 := by
    simp only [lead,     outerLead_length]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix,  List.append_nil, List.append_assoc]
  have hprefix : leading.length = 353 := by
    simp only [leading, initBlock_length, boundedTest_length, initRow_length, matchTest_length, jumpTo, matched_length, innerTail_length,  List.length_append, List.length_cons, List.length_nil]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix (.jumpIfZero .flag .index) 353
    hlayout hprefix (by dsimp [lead, matchLead, innerLead, outerLead, jumpTo, List.take_succ_cons,
      List.take_zero, initBlock, setCache, setFlat, storeFlat, loadFlat, incrementFlat, initRow, writeParent, loadParent, matched, writeChild, writeDegree, incrementCache, loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]; simp) state hpc hactive
  simpa only [hlength, hlead] using hh

end Containing

private theorem jump_heap (rom : PhysicalROM) (target : Nat) (state : NatState) :
    (runOps rom (jumpTo target) state).heap = state.heap := by
  simp [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]

private theorem jump_pc (rom : PhysicalROM) (target : Nat) (state : NatState) :
    (runOps rom (jumpTo target) state).pc = 5 * target := by
  simp [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem innerTail_eq (start : Nat) : innerTail start = incrementCache 2 ++ jumpTo (start + 127) := by
  simp only [innerTail, innerLead, jumpTo, List.take_succ_cons, List.take_zero,
    List.append_assoc, List.cons_append, List.nil_append]

theorem outerTail_eq (start : Nat) :
    outerTail start = writeDegree ++ incrementCache 1 ++ jumpTo (start + 35) := by
  simp only [outerTail, outerLead, jumpTo, List.take_succ_cons, List.take_zero,
    List.append_assoc, List.cons_append, List.nil_append]

theorem innerTail_values (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState) :
    let result := runOps (rawIncidenceROM q full) (innerTail start) state
    result.heap = Function.update state.heap (workspaceBase full.length q + 2)
        (state.heap (workspaceBase full.length q + 2) + 1) ∧
      result.pc = 5 * (start + 127) ∧ result.halted = state.halted := by
  constructor
  · simp only [innerTail_eq, runOps_append, jump_heap, incrementCache_heap]
  · exact ⟨by rw [innerTail_eq, runOps_append, jump_pc], runOps_halted _ _ _⟩

theorem outerTail_values (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (htarget : 3 + state.heap 0 + state.heap 5 + state.heap (workspaceBase full.length q + 1) <
      workspaceBase full.length q) :
    let result := runOps (rawIncidenceROM q full) (outerTail start) state
    result.heap = Function.update
        (Function.update state.heap (3 + state.heap 0 + state.heap 5 + state.heap (workspaceBase full.length q + 1))
          (state.heap (workspaceBase full.length q + 3)))
        (workspaceBase full.length q + 1) (state.heap (workspaceBase full.length q + 1) + 1) ∧
      result.pc = 5 * (start + 35) ∧ result.halted = state.halted := by
  constructor
  · simp only [outerTail_eq, runOps_append, jump_heap, incrementCache_heap, writeDegree_heap]
    simp (disch := omega)
  · exact ⟨by rw [outerTail_eq, runOps_append, jump_pc], runOps_halted _ _ _⟩

theorem matched_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (htarget : 3 + state.heap 0 + state.heap 1 + state.heap (flatAddress full.length q) < workspaceBase full.length q) :
    (runOps (rawIncidenceROM q full) matched state).heap =
      Function.update (Function.update
        (Function.update state.heap (3 + state.heap 0 + state.heap 1 + state.heap (flatAddress full.length q))
          (state.heap (workspaceBase full.length q + 2)))
        (workspaceBase full.length q + 3) (state.heap (workspaceBase full.length q + 3) + 1))
        (flatAddress full.length q) (state.heap (flatAddress full.length q) + 1) := by
  simp only [matched, runOps_append, incrementFlat_heap, incrementCache_heap, writeChild_heap]
  dsimp only [flatAddress] at htarget
  simp (disch := omega) [flatAddress]

def size (q : Nat) (full : List (Finset (Fin q))) : Nat := (prepareNormalization q full).indexed.nodes.size

def internalStart (q : Nat) (full : List (Finset (Fin q))) : Nat := 3 + (givenTreeROM q full).input.length

def childrenStart (q : Nat) (full : List (Finset (Fin q))) : Nat := internalStart q full + 2 * size q full

def endAddress (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  childrenStart q full + (givenTreeROM q full).children.length

def parentWords (q : Nat) (full : List (Finset (Fin q))) (child : Nat) : Nat :=
  (givenTreeROM q full).internal.getD child 0

structure InputSpec (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop where
  headers : HeaderSpec q full state
  parents : ∀ child < size q full, state.heap (parentAddress full.length q child) = parentWords q full child

theorem InputSpec.header0 {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (h : InputSpec q full state) : state.heap 0 = (givenTreeROM q full).input.length := by
  simpa only [List.getD_cons_zero, RawTreeSerialization.givenTreeROM_input_length] using h.headers 0 (by decide)

theorem InputSpec.header1 {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (h : InputSpec q full state) : state.heap 1 = 2 * size q full := by
  simpa [size] using h.headers 1 (by decide)

theorem InputSpec.header5 {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (h : InputSpec q full state) : state.heap 5 = size q full := h.headers.count

theorem internalStart_ge_six (q : Nat) (full : List (Finset (Fin q))) : 6 ≤ internalStart q full := by
  unfold internalStart
  rw [RawTreeSerialization.givenTreeROM_input_length]
  omega

theorem endAddress_lt_base (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full) :
    endAddress q full < workspaceBase full.length q := by
  have hlen := RawTreeSerialization.serialize_givenTreeROM_length_le q full hq hl
  have heq : endAddress q full = (serializeROM (givenTreeROM q full)).length := by
    rw [RawTreeSerialization.serializeROM_length]
    simp only [endAddress, childrenStart, internalStart, size, PhysicalROM.size,
      RawTreeSerialization.givenTreeROM_internal_length]
    omega
  rw [heq]
  unfold workspaceBase candidateCount
  omega

def Protected (q : Nat) (full : List (Finset (Fin q))) (address : Nat) : Prop :=
  address ≠ workspaceBase full.length q + 1 ∧ address ≠ workspaceBase full.length q + 2 ∧
    address ≠ workspaceBase full.length q + 3 ∧ address ≠ flatAddress full.length q ∧
      (address < internalStart q full ∨ endAddress q full ≤ address)

def Frame (q : Nat) (full : List (Finset (Fin q))) (before after : NatState) : Prop :=
  ∀ address, Protected q full address → after.heap address = before.heap address

theorem Frame.refl (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Frame q full state state :=
  fun _ _ => rfl

theorem Frame.trans {q : Nat} {full : List (Finset (Fin q))} {one two three : NatState}
    (h12 : Frame q full one two) (h23 : Frame q full two three) : Frame q full one three := by
  intro address hp
  exact (h23 address hp).trans (h12 address hp)

theorem InputSpec.of_frame {q : Nat} {full : List (Finset (Fin q))} {before after : NatState}
    (hq : 0 < q) (hl : LaminarSchedule full) (hspec : InputSpec q full before)
    (hframe : Frame q full before after) : InputSpec q full after := by
  have hb := workspaceBase_ge full.length q
  have ht : size q full ≤ candidateCount full.length q := prepared_indexed_size_le q full
  have hend := endAddress_lt_base q full hq hl
  constructor
  · intro address ha
    rw [hframe address (by
      have hs := internalStart_ge_six q full
      refine ⟨by omega, by omega, by omega, ?_, Or.inl (by omega)⟩
      unfold flatAddress
      omega)]
    exact hspec.headers address ha
  · intro child hc
    rw [hframe (parentAddress full.length q child) (by
      unfold Protected parentAddress flatAddress
      omega)]
    exact hspec.parents child hc

structure CursorReady (q : Nat) (full : List (Finset (Fin q))) (node child pointer : Nat) (state : NatState) : Prop where
  input : InputSpec q full state
  node_cell : state.heap (workspaceBase full.length q + 1) = node
  child_cell : state.heap (workspaceBase full.length q + 2) = child
  pc : state.pc = pointer
  active : state.halted = false

def bitSteps (words : Nat → Nat) (node child : Nat) : Nat :=
  if words child = node + 1 then 223 else 114

def bitHeap (q : Nat) (full : List (Finset (Fin q))) (node child : Nat) (state : NatState) : Nat → Nat :=
  Function.update
    (if parentWords q full child = node + 1 then
      Function.update (Function.update
        (Function.update state.heap (childrenStart q full + state.heap (flatAddress full.length q)) child)
        (workspaceBase full.length q + 3) (state.heap (workspaceBase full.length q + 3) + 1))
        (flatAddress full.length q) (state.heap (flatAddress full.length q) + 1)
    else state.heap)
    (workspaceBase full.length q + 2) (child + 1)

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 427 ≤ containing.length)
  (hcode : ∀ position < 427, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem inner_iteration (node child : Nat) (state : NatState)
    (ready : CursorReady q full node child (5 * (start + 127)) state)
    (hc : child < size q full)
    (hwrite : parentWords q full child = node + 1 →
      childrenStart q full + state.heap (flatAddress full.length q) < workspaceBase full.length q) :
    let result := natRun (rawIncidenceROM q full) containing (bitSteps (parentWords q full) node child) state
    result.heap = bitHeap q full node child state ∧
      result.pc = 5 * (start + 127) ∧ result.halted = false := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (boundedTest 2 5 (start + 353)) state
  have ht := boundedTest_values q full 2 5 (start + 353) state
  dsimp only at ht
  have hth : tested.heap = state.heap := ht.1
  have htp : tested.pc = 5 * (start + 147) := by
    have hp := ht.2.1
    rw [ready.input.header5, ready.child_cell, ite_eq_right (Nat.sub_ne_zero_of_lt hc), ready.pc] at hp
    dsimp only [tested]
    omega
  have hta : tested.halted = false := ht.2.2.trans ready.active
  let checked := runOps rom (matchTest start) tested
  have hm := matchTest_values q full start tested
  dsimp only at hm
  have hch : checked.heap = state.heap := hm.1.trans hth
  have hca : checked.halted = false := hm.2.1.trans hta
  have hcp : checked.pc = if parentWords q full child = node + 1 then 5 * (start + 206) else 5 * (start + 203) := by
    calc
      checked.pc = if tested.heap (parentAddress full.length q (tested.heap (workspaceBase full.length q + 2))) =
          tested.heap (workspaceBase full.length q + 1) + 1 then 5 * (start + 206) else tested.pc + 280 := hm.2.2
      _ = _ := by
        rw [hth, ready.child_cell, ready.node_cell, ready.input.parents child hc, htp]
        split <;> omega
  by_cases heq : parentWords q full child = node + 1
  · let written := runOps rom matched checked
    have hs : 3 + checked.heap 0 + checked.heap 1 + checked.heap (flatAddress full.length q) < workspaceBase full.length q := by
      rw [hch, ready.input.header0, ready.input.header1]
      exact hwrite heq
    have hw := matched_heap q full checked hs
    have hwp : written.pc = 5 * (start + 318) := by
      rw [show written = runOps _ _ _ from rfl,
        runOps_pc _ _ _ (by
          dsimp [matched, writeChild, loadCache, loadFlat, incrementCache, incrementFlat, storeFlat,
            storeCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]
          simp), matched_length, hcp, ite_eq_left heq]
      omega
    have hwa : written.halted = false := (runOps_halted _ _ _).trans hca
    let finished := runOps rom (innerTail start) written
    have hf := innerTail_values q full start written
    dsimp only at hf
    have hfh : finished.heap = bitHeap q full node child state := by
      have hdst := hwrite heq
      dsimp only [childrenStart, internalStart, flatAddress] at hdst
      have hh := hf.1
      rw [hw, hch, ready.input.header0, ready.input.header1, ready.child_cell] at hh
      dsimp only [bitHeap]
      rw [ite_eq_left heq]
      rw [hh]
      simp only [childrenStart, internalStart]
      simp (disch := omega) [flatAddress, ready.child_cell]
    have hrun : natRun rom containing (bitSteps (parentWords q full) node child) state = finished := by
      rw [bitSteps, ite_eq_left heq, show 223 = 20 + (56 + (112 + 35)) from rfl,
        natRun_add, run_innerTest rom containing start hbound hcode state ready.pc ready.active]
      change natRun rom containing (56 + (112 + 35)) tested = _
      rw [natRun_add, run_matchTest rom containing start hbound hcode tested htp hta]
      change natRun rom containing (112 + 35) checked = _
      rw [natRun_add, run_matched rom containing start hbound hcode checked (by simpa only [ite_eq_left heq] using hcp) hca]
      exact run_innerTail rom containing start hbound hcode written hwp hwa
    dsimp only
    rw [hrun]
    exact ⟨hfh, hf.2.1, hf.2.2.trans hwa⟩
  · let skipped := runOps rom (jumpTo (start + 318)) checked
    have hsh : skipped.heap = state.heap := (jump_heap _ _ _).trans hch
    have hsp : skipped.pc = 5 * (start + 318) := jump_pc _ _ _
    have hsa : skipped.halted = false := (runOps_halted _ _ _).trans hca
    let finished := runOps rom (innerTail start) skipped
    have hf := innerTail_values q full start skipped
    dsimp only at hf
    have hfh : finished.heap = bitHeap q full node child state := by
      have hh := hf.1
      rw [hsh, ready.child_cell] at hh
      exact hh.trans (by simp only [bitHeap, ite_eq_right heq])
    have hrun : natRun rom containing (bitSteps (parentWords q full) node child) state = finished := by
      rw [bitSteps, ite_eq_right heq, show 114 = 20 + (56 + (3 + 35)) from rfl,
        natRun_add, run_innerTest rom containing start hbound hcode state ready.pc ready.active]
      change natRun rom containing (56 + (3 + 35)) tested = _
      rw [natRun_add, run_matchTest rom containing start hbound hcode tested htp hta]
      change natRun rom containing (3 + 35) checked = _
      rw [natRun_add, run_skipMatch rom containing start hbound hcode checked (by simpa only [ite_eq_right heq] using hcp) hca]
      exact run_innerTail rom containing start hbound hcode skipped hsp hsa
    dsimp only
    rw [hrun]
    exact ⟨hfh, hf.2.1, hf.2.2.trans hsa⟩

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenRAM
