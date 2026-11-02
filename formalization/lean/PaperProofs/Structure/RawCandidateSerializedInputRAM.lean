module

public import PaperProofs.Structure.RawCandidateWorkspaceBaseRAM
public import PaperProofs.Structure.RawCandidateIncidenceBlock
public import PaperProofs.Structure.RawTreeSerialization

/-! Actual fixed-code materialization of the three serialization lengths
and the complete input region.  Cache addresses are recovered from readonly
dimensions on every access.  Mutable output cell 8 is never a base pointer.
Controls B+1/B+2/B+3 hold raw cursor then node / tool / N*q respectively. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateWorkspaceInit

def loadCache (target : Register) (offset : Nat) : List PackingOp :=
  RawCandidateWorkspaceBaseRAM.program ++
    [.base (.base (.constant .index offset)), .base (.base (.add .address .address .index)),
      .base (.base (.loadHeap target .address))]

def storeCache (offset : Nat) : List PackingOp :=
  RawCandidateWorkspaceBaseRAM.program ++
    [.base (.base (.constant .index offset)), .base (.base (.add .address .address .index)),
      .base (.base (.storeHeap .address .value))]

def setCache (offset value : Nat) : List PackingOp :=
  [.base (.base (.constant .value value))] ++ storeCache offset

def incrementCache (offset : Nat) : List PackingOp :=
  loadCache .value offset ++ [.base (.base (.constant .index 1)), .base (.base (.add .value .value .index))] ++
    storeCache offset

def loadNodeCount : List PackingOp :=
  RawCandidateWorkspaceBaseRAM.program ++
    [.base (.base (.constant .index 4)), .arithmetic .multiply .index .total .index,
     .base (.base (.add .address .address .index)), .base (.base (.constant .index 4)),
     .base (.base (.add .address .address .index)), .base (.base (.loadHeap .value .address))]

def readOrd : List PackingOp :=
  loadCache .old 1 ++ RawCandidateWorkspaceBaseRAM.program ++
    [.base (.base (.constant .index 2)), .arithmetic .multiply .index .total .index,
     .base (.base (.add .address .address .index)), .base (.base (.constant .index 4)),
     .base (.base (.add .address .address .index)), .base (.base (.add .address .address .old)),
     .base (.base (.loadHeap .old .address))]

def headers : List PackingOp :=
  loadNodeCount ++ storeCell .value 5 ++
    [.base (.base (.constant .index 0)), .base (.base (.loadROM .input .old .index)),
     .base (.base (.constant .index 1)), .base (.base (.loadROM .input .fresh .index))] ++
    storeCell .old 3 ++ storeCell .fresh 4 ++
    [.arithmetic .multiply .total .old .fresh, .base (.base (.minimum .value .total .total))] ++
    storeCache 3 ++ loadCache .total 3 ++ loadCell .old 5 ++
    [.arithmetic .multiply .old .old .fresh, .base (.base (.add .total .total .old)),
     .base (.base (.constant .index 3)), .base (.base (.add .total .total .index))] ++ storeCell .total 0 ++
    loadCell .total 5 ++ [.base (.base (.add .total .total .total))] ++ storeCell .total 1 ++
    loadCell .total 5 ++ [.base (.base (.constant .index 1)), .base (.subtract .total .total .index)] ++
    storeCell .total 2

def rawTest (exit : Nat) : List PackingOp :=
  loadCache .old 1 ++ loadCache .total 3 ++
    [.base (.subtract .flag .total .old), .base (.base (.constant .index (5 * exit))),
     .jumpIfZero .flag .index]

def rawBody (start : Nat) : List PackingOp :=
  loadCache .old 1 ++
    [.base (.base (.constant .index 2)), .base (.base (.add .index .index .old)),
     .base (.base (.loadROM .input .value .index)), .base (.base (.constant .address 6)),
     .base (.base (.add .address .address .old)), .base (.base (.storeHeap .address .value))] ++
    incrementCache 1 ++ jumpTo (start + 95)

def boundedTest (counter header exit : Nat) : List PackingOp :=
  loadCache .total counter ++ loadCell .old header ++
    [.base (.subtract .flag .old .total), .base (.base (.constant .index (5 * exit))),
     .jumpIfZero .flag .index]

def arguments : List PackingOp := readOrd ++ loadCache .fresh 2

def writeNode : List PackingOp :=
  loadCache .old 1 ++
    [.arithmetic .multiply .old .old .flag, .base (.base (.add .old .old .fresh))] ++
    loadCache .fresh 3 ++
    [.base (.base (.add .old .old .fresh)), .base (.base (.constant .address 6)),
     .base (.base (.add .address .address .old)), .base (.base (.storeHeap .address .value))]

def toolTail (start : Nat) : List PackingOp := writeNode ++ incrementCache 2 ++ jumpTo (start + 236)

def rowTail (start : Nat) : List PackingOp := incrementCache 1 ++ jumpTo (start + 200)

def programAt (start : Nat) : List PackingOp :=
  headers ++ setCache 1 0 ++ rawTest (start + 184) ++ rawBody start ++ setCache 1 0 ++
    boundedTest 1 5 (start + 443) ++ setCache 2 0 ++ boundedTest 2 4 (start + 408) ++ arguments ++
    RawCandidateIncidenceBlock.programAt (start + 305) ++ toolTail start ++ rowTail start

theorem loadCache_length (target : Register) (offset : Nat) : (loadCache target offset).length = 15 := by
  simp only [loadCache, RawCandidateWorkspaceBaseRAM.program_length, List.length_append,
    List.length_cons, List.length_nil]

theorem storeCache_length (offset : Nat) : (storeCache offset).length = 15 := by
  simp only [storeCache, RawCandidateWorkspaceBaseRAM.program_length, List.length_append,
    List.length_cons, List.length_nil]

theorem setCache_length (offset value : Nat) : (setCache offset value).length = 16 := by
  simp only [setCache, storeCache_length, List.length_append, List.length_cons, List.length_nil]

theorem incrementCache_length (offset : Nat) : (incrementCache offset).length = 32 := by
  simp only [incrementCache, loadCache_length, storeCache_length, List.length_append,
    List.length_cons, List.length_nil]

theorem loadNodeCount_length : loadNodeCount.length = 18 := by
  simp only [loadNodeCount, RawCandidateWorkspaceBaseRAM.program_length, List.length_append,
    List.length_cons, List.length_nil]

theorem readOrd_length : readOrd.length = 34 := by
  simp only [readOrd, loadCache_length, RawCandidateWorkspaceBaseRAM.program_length,
    List.length_append, List.length_cons, List.length_nil]

theorem headers_length : headers.length = 79 := by
  simp only [headers, loadNodeCount_length, storeCache_length, loadCache_length, loadCell, storeCell,
    List.length_append, List.length_cons, List.length_nil]

theorem rawTest_length (exit : Nat) : (rawTest exit).length = 33 := by
  simp only [rawTest, loadCache_length, List.length_append, List.length_cons, List.length_nil]

theorem rawBody_length (start : Nat) : (rawBody start).length = 56 := by
  simp only [rawBody, loadCache_length, incrementCache_length, jumpTo,
    List.length_append, List.length_cons, List.length_nil]

theorem boundedTest_length (counter header exit : Nat) : (boundedTest counter header exit).length = 20 := by
  simp only [boundedTest, loadCache_length, loadCell, List.length_append, List.length_cons, List.length_nil]

theorem arguments_length : arguments.length = 49 := by
  simp only [arguments, readOrd_length, loadCache_length, List.length_append]

theorem writeNode_length : writeNode.length = 36 := by
  simp only [writeNode, loadCache_length, List.length_append, List.length_cons, List.length_nil]

theorem toolTail_length (start : Nat) : (toolTail start).length = 71 := by
  simp only [toolTail, writeNode_length, incrementCache_length, jumpTo,
    List.length_append, List.length_cons, List.length_nil]

theorem rowTail_length (start : Nat) : (rowTail start).length = 35 := by
  simp only [rowTail, incrementCache_length, jumpTo, List.length_append, List.length_cons, List.length_nil]

theorem programAt_length (start : Nat) : (programAt start).length = 443 := by
  simp only [programAt, List.length_append, headers_length, setCache_length, rawTest_length, rawBody_length,
    boundedTest_length, arguments_length, RawCandidateIncidenceBlock.programAt_length, toolTail_length, rowTail_length]

def nodeCountAddress (N q : Nat) : Nat := workspaceBase N q + 4 + 4 * candidateCount N q

def ordAddress (N q node : Nat) : Nat := workspaceBase N q + 4 + 2 * candidateCount N q + node

def prefixLength (N q count : Nat) : Nat := 6 + N * q + count * q

/-- Cache handoff only; the bit answers themselves are not supplied. -/
structure InputSpec (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop where
  node_count : state.heap (nodeCountAddress full.length q) = (prepareNormalization q full).indexed.nodes.size
  ord_legal : ∀ node < (prepareNormalization q full).indexed.nodes.size,
    state.heap (ordAddress full.length q node) < candidateCount full.length q
  ord_support : ∀ node < (prepareNormalization q full).indexed.nodes.size,
    (RawCandidateOrder.candidateSupports q full).getD (state.heap (ordAddress full.length q node)) ∅ =
      (prepareNormalization q full).order.getD node ∅

theorem prefixLength_lt_base (q : Nat) (full : List (Finset (Fin q))) :
    prefixLength full.length q (prepareNormalization q full).indexed.nodes.size < workspaceBase full.length q := by
  have ht := prepared_indexed_size_le q full
  have hmul := Nat.mul_le_mul_right q ht
  unfold prefixLength workspaceBase candidateCount
  nlinarith

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

/-- A proved state summary of the existing twelve instructions, not an ISA
operation and not an extra machine input. -/
def recovered (N q : Nat) (state : NatState) : NatState :=
  { state with
    register := fun reg => match reg with
      | .old => state.register .old
      | .fresh => state.register .fresh
      | .value => state.register .value
      | .total => candidateCount N q
      | .flag => q
      | .address => workspaceBase N q
      | .index => 16
    pc := state.pc + 60 }

theorem base_runOps (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    runOps (rawIncidenceROM q full) RawCandidateWorkspaceBaseRAM.program state = recovered full.length q state := by
  apply state_ext
  · funext reg
    cases reg <;> simp [recovered, RawCandidateWorkspaceBaseRAM.program, runOps, natExecuteOp,
      natArithmetic, Op.execute, Instruction.execute, raw_header_N, raw_header_q,
      candidateCount, workspaceBase, Nat.mul_assoc, Nat.mul_comm]
  · simp [recovered, RawCandidateWorkspaceBaseRAM.program, runOps, natExecuteOp,
      Op.execute, Instruction.execute]
  · simp [recovered, RawCandidateWorkspaceBaseRAM.program, runOps, natExecuteOp,
      Op.execute, Instruction.execute]
  · simp [recovered, RawCandidateWorkspaceBaseRAM.program, runOps, natExecuteOp,
      Op.execute, Instruction.execute]

def loaded (N q : Nat) (target : Register) (offset : Nat) (state : NatState) : NatState :=
  { recovered N q state with
    register := Function.update
      (Function.update (Function.update (recovered N q state).register .index offset)
        .address (workspaceBase N q + offset)) target (state.heap (workspaceBase N q + offset))
    pc := state.pc + 75 }

theorem loadCache_runOps (q : Nat) (full : List (Finset (Fin q)))
    (target : Register) (offset : Nat) (state : NatState) :
    runOps (rawIncidenceROM q full) (loadCache target offset) state = loaded full.length q target offset state := by
  rw [loadCache, runOps_append, base_runOps]
  apply state_ext
  · funext reg
    cases reg <;> cases target <;>
      simp [loaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [loaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [loaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [loaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]

def stored (N q offset : Nat) (state : NatState) : NatState :=
  { recovered N q state with
    register := Function.update
      (Function.update (recovered N q state).register .index offset) .address (workspaceBase N q + offset)
    heap := Function.update state.heap (workspaceBase N q + offset) (state.register .value)
    pc := state.pc + 75 }

theorem storeCache_runOps (q : Nat) (full : List (Finset (Fin q))) (offset : Nat) (state : NatState) :
    runOps (rawIncidenceROM q full) (storeCache offset) state = stored full.length q offset state := by
  rw [storeCache, runOps_append, base_runOps]
  apply state_ext
  · funext reg
    cases reg <;> simp [stored, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [stored, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [stored, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]
  · simp [stored, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem loadNodeCount_values (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    let result := runOps (rawIncidenceROM q full) loadNodeCount state
    result.register .value = state.heap (nodeCountAddress full.length q) ∧
      result.heap = state.heap ∧ result.pc = state.pc + 90 ∧ result.halted = state.halted := by
  simp only [loadNodeCount, runOps_append, base_runOps]
  simp [recovered, nodeCountAddress, runOps, natExecuteOp, natArithmetic, Op.execute,
    Instruction.execute, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

theorem incrementCache_heap (q : Nat) (full : List (Finset (Fin q))) (offset : Nat) (state : NatState) :
    (runOps (rawIncidenceROM q full) (incrementCache offset) state).heap =
      Function.update state.heap (workspaceBase full.length q + offset)
        (state.heap (workspaceBase full.length q + offset) + 1) := by
  simp only [incrementCache, runOps_append, loadCache_runOps, storeCache_runOps]
  simp [loaded, stored, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]

def headerHeap (N q count : Nat) (heap : Nat → Nat) : Nat → Nat :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update (Function.update heap 5 count) 3 N) 4 q)
          (workspaceBase N q + 3) (N * q))
        0 (3 + N * q + count * q))
      1 (2 * count))
    2 (count - 1)

theorem headers_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    (runOps (rawIncidenceROM q full) headers state).heap =
      headerHeap full.length q (state.heap (nodeCountAddress full.length q)) state.heap := by
  have hb := workspaceBase_ge full.length q
  simp only [headers, runOps_append, loadNodeCount, base_runOps, loadCache_runOps, storeCache_runOps]
  simp (disch := first | omega | decide) [loaded, stored, recovered, headerHeap,
    nodeCountAddress, loadCell, storeCell, runOps, natExecuteOp, natArithmetic, Op.execute,
    Instruction.execute, raw_header_N, raw_header_q, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc, two_mul]

theorem readOrd_values (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    let result := runOps (rawIncidenceROM q full) readOrd state
    result.register .old = state.heap (ordAddress full.length q (state.heap (workspaceBase full.length q + 1))) ∧
      result.heap = state.heap ∧ result.pc = state.pc + 170 ∧ result.halted = state.halted := by
  simp only [readOrd, runOps_append, loadCache_runOps, base_runOps]
  simp [loaded, recovered, ordAddress, runOps, natExecuteOp, natArithmetic, Op.execute,
    Instruction.execute, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

theorem arguments_values (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    let result := runOps (rawIncidenceROM q full) arguments state
    result.register .old = state.heap (ordAddress full.length q (state.heap (workspaceBase full.length q + 1))) ∧
      result.register .fresh = state.heap (workspaceBase full.length q + 2) ∧
      result.heap = state.heap ∧ result.pc = state.pc + 245 ∧ result.halted = state.halted := by
  have h := readOrd_values q full state
  dsimp only at h
  simp only [arguments, runOps_append, loadCache_runOps]
  simp [loaded, recovered, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem rawTest_values (q : Nat) (full : List (Finset (Fin q))) (exit : Nat) (state : NatState) :
    let result := runOps (rawIncidenceROM q full) (rawTest exit) state
    result.heap = state.heap ∧
      result.pc = (if state.heap (workspaceBase full.length q + 3) - state.heap (workspaceBase full.length q + 1) = 0
        then 5 * exit else state.pc + 165) ∧ result.halted = state.halted := by
  simp only [rawTest, runOps_append, loadCache_runOps]
  simp [loaded, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute, Nat.add_assoc]

theorem boundedTest_values (q : Nat) (full : List (Finset (Fin q)))
    (counter header exit : Nat) (state : NatState) :
    let result := runOps (rawIncidenceROM q full) (boundedTest counter header exit) state
    result.heap = state.heap ∧
      result.pc = (if state.heap header - state.heap (workspaceBase full.length q + counter) = 0
        then 5 * exit else state.pc + 100) ∧ result.halted = state.halted := by
  simp only [boundedTest, runOps_append, loadCache_runOps]
  simp [loaded, recovered, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, Nat.add_assoc]

theorem setCache_heap (q : Nat) (full : List (Finset (Fin q))) (offset value : Nat) (state : NatState) :
    (runOps (rawIncidenceROM q full) (setCache offset value) state).heap =
      Function.update state.heap (workspaceBase full.length q + offset) value := by
  simp only [setCache, runOps_append, storeCache_runOps]
  simp [stored, recovered, runOps, natExecuteOp, Op.execute, Instruction.execute]

private theorem jumpTo_heap (rom : PhysicalROM) (target : Nat) (state : NatState) :
    (runOps rom (jumpTo target) state).heap = state.heap := by
  simp [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]

private theorem jumpTo_pc (rom : PhysicalROM) (target : Nat) (state : NatState) :
    (runOps rom (jumpTo target) state).pc = 5 * target := by
  simp [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem rawBody_values (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hsep : 6 + state.heap (workspaceBase full.length q + 1) < workspaceBase full.length q) :
    let offset := state.heap (workspaceBase full.length q + 1)
    let result := runOps (rawIncidenceROM q full) (rawBody start) state
    result.heap = Function.update
      (Function.update state.heap (6 + offset) ((rawIncidenceROM q full).semantic.read .input (2 + offset)))
      (workspaceBase full.length q + 1) (offset + 1) ∧
      result.pc = 5 * (start + 95) ∧ result.halted = state.halted := by
  constructor
  · simp only [rawBody, runOps_append, jumpTo_heap, incrementCache_heap, loadCache_runOps]
    simp (disch := first | omega | decide) [loaded, recovered, runOps, natExecuteOp,
      Op.execute, Instruction.execute]
  · constructor
    · simp only [rawBody, runOps_append, jumpTo_pc]
    · exact runOps_halted _ _ _

theorem writeNode_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    (runOps (rawIncidenceROM q full) writeNode state).heap = Function.update state.heap
      (6 + state.heap (workspaceBase full.length q + 3) +
        state.heap (workspaceBase full.length q + 1) * q + state.register .fresh) (state.register .value) := by
  simp only [writeNode, runOps_append, loadCache_runOps]
  simp [loaded, recovered, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem toolTail_values (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hsep : 6 + state.heap (workspaceBase full.length q + 3) +
      state.heap (workspaceBase full.length q + 1) * q + state.register .fresh < workspaceBase full.length q) :
    let destination := 6 + state.heap (workspaceBase full.length q + 3) +
      state.heap (workspaceBase full.length q + 1) * q + state.register .fresh
    let result := runOps (rawIncidenceROM q full) (toolTail start) state
    result.heap = Function.update (Function.update state.heap destination (state.register .value))
      (workspaceBase full.length q + 2) (state.heap (workspaceBase full.length q + 2) + 1) ∧
      result.pc = 5 * (start + 236) ∧ result.halted = state.halted := by
  constructor
  · simp only [toolTail, runOps_append, jumpTo_heap, incrementCache_heap, writeNode_heap]
    simp (disch := omega)
  · constructor
    · simp only [toolTail, runOps_append, jumpTo_pc]
    · exact runOps_halted _ _ _

theorem rowTail_values (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState) :
    let result := runOps (rawIncidenceROM q full) (rowTail start) state
    result.heap = Function.update state.heap (workspaceBase full.length q + 1)
      (state.heap (workspaceBase full.length q + 1) + 1) ∧
      result.pc = 5 * (start + 200) ∧ result.halted = state.halted := by
  constructor
  · simp only [rowTail, runOps_append, jumpTo_heap, incrementCache_heap]
  · constructor
    · simp only [rowTail, runOps_append, jumpTo_pc]
    · exact runOps_halted _ _ _

def paddingOp : PackingOp := .base (.base (.constant .value 0))

private theorem getD_middle (left middle right : List PackingOp) (position : Nat)
    (hp : position < middle.length) :
    (left ++ middle ++ right).getD (left.length + position) paddingOp = middle.getD position paddingOp := by
  rw [List.getD_append (left ++ middle) right paddingOp _ (by simp; omega),
    List.getD_append_right left middle paddingOp _ (by omega), Nat.add_sub_cancel_left]

section Containing

variable (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
  (hbound : start + 443 ≤ containing.length)
  (hcode : ∀ position < 443, containing.getD (start + position) paddingOp =
    (programAt start).getD position paddingOp)

include hbound hcode

private theorem containing_slice (leading block suffix : List PackingOp) (offset : Nat)
    (hlayout : programAt start = leading ++ block ++ suffix) (hprefix : leading.length = offset) :
    start + offset + block.length ≤ containing.length ∧
      ∀ position < block.length, containing.getD ((start + offset) + position) paddingOp = block.getD position paddingOp := by
  have hspan : offset + block.length ≤ 443 := by
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

theorem run_headers (state : NatState) (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    natRun rom containing 79 state = runOps rom headers state := by
  let suffix := setCache 1 0 ++ rawTest (start + 184) ++ rawBody start ++ setCache 1 0 ++
    boundedTest 1 5 (start + 443) ++ setCache 2 0 ++ boundedTest 2 4 (start + 408) ++ arguments ++
    RawCandidateIncidenceBlock.programAt (start + 305) ++ toolTail start ++ rowTail start
  have hlayout : programAt start = [] ++ headers ++ suffix := by
    simp only [programAt, suffix, List.nil_append, List.append_assoc]
  exact run_straight_layout rom containing start hbound hcode [] headers suffix 0 hlayout rfl
    (by simp [headers, loadNodeCount, loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program,
      loadCell, storeCell, NoJump]) state (by simpa only [Nat.add_zero] using hpc) hactive

theorem run_rawTest (state : NatState) (hpc : state.pc = 5 * (start + 95)) (hactive : state.halted = false) :
    natRun rom containing 33 state = runOps rom (rawTest (start + 184)) state := by
  let leading := headers ++ setCache 1 0
  let suffix := rawBody start ++ setCache 1 0 ++ boundedTest 1 5 (start + 443) ++ setCache 2 0 ++
    boundedTest 2 4 (start + 408) ++ arguments ++ RawCandidateIncidenceBlock.programAt (start + 305) ++
    toolTail start ++ rowTail start
  let lead := loadCache .old 1 ++ loadCache .total 3 ++
    [.base (.subtract .flag .total .old), .base (.base (.constant .index (5 * (start + 184))))]
  have hlead : lead ++ [.jumpIfZero .flag .index] = rawTest (start + 184) := by
    simp only [lead, rawTest, List.append_assoc, List.cons_append, List.nil_append]
  have hlen : lead.length = 32 := by
    simp only [lead, loadCache_length, List.length_append, List.length_cons, List.length_nil]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 95 := by simp only [leading, List.length_append, headers_length, setCache_length]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix (.jumpIfZero .flag .index)
    95 hlayout hp (by simp [lead, loadCache, RawCandidateWorkspaceBaseRAM.program, NoJump]) state hpc hactive
  simpa only [hlen, hlead] using hh

theorem run_rawInit (state : NatState) (hpc : state.pc = 5 * (start + 79)) (hactive : state.halted = false) :
    natRun rom containing 16 state = runOps rom (setCache 1 0) state := by
  let suffix := rawTest (start + 184) ++ rawBody start ++ setCache 1 0 ++
    boundedTest 1 5 (start + 443) ++ setCache 2 0 ++ boundedTest 2 4 (start + 408) ++ arguments ++
    RawCandidateIncidenceBlock.programAt (start + 305) ++ toolTail start ++ rowTail start
  have hlayout : programAt start = headers ++ setCache 1 0 ++ suffix := by
    simp only [programAt, suffix, List.append_assoc]
  exact run_straight_layout rom containing start hbound hcode headers (setCache 1 0) suffix 79
    hlayout headers_length
    (by simp [setCache, storeCache, RawCandidateWorkspaceBaseRAM.program, NoJump]) state hpc hactive

theorem run_rawBody (state : NatState) (hpc : state.pc = 5 * (start + 128)) (hactive : state.halted = false) :
    natRun rom containing 56 state = runOps rom (rawBody start) state := by
  let leading := headers ++ setCache 1 0 ++ rawTest (start + 184)
  let suffix := setCache 1 0 ++ boundedTest 1 5 (start + 443) ++ setCache 2 0 ++
    boundedTest 2 4 (start + 408) ++ arguments ++ RawCandidateIncidenceBlock.programAt (start + 305) ++
    toolTail start ++ rowTail start
  let lead := loadCache .old 1 ++
    [.base (.base (.constant .index 2)), .base (.base (.add .index .index .old)),
     .base (.base (.loadROM .input .value .index)), .base (.base (.constant .address 6)),
     .base (.base (.add .address .address .old)), .base (.base (.storeHeap .address .value))] ++
    incrementCache 1 ++ (jumpTo (start + 95)).take 2
  have hlead : lead ++ [.jumpIfZero .flag .index] = rawBody start := by
    simp only [lead, rawBody, jumpTo, List.take_succ_cons, List.take_zero,
      List.append_assoc, List.cons_append, List.nil_append]
  have hlen : lead.length = 55 := by
    simp only [lead, loadCache_length, incrementCache_length, jumpTo, List.take_succ_cons, List.take_zero,
      List.length_append, List.length_cons, List.length_nil]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 128 := by
    simp only [leading, List.length_append, headers_length, setCache_length, rawTest_length]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix (.jumpIfZero .flag .index)
    128 hlayout hp
    (by simp [lead, loadCache, incrementCache, storeCache, RawCandidateWorkspaceBaseRAM.program, jumpTo, NoJump])
    state hpc hactive
  simpa only [hlen, hlead] using hh

theorem run_nodeInit (state : NatState) (hpc : state.pc = 5 * (start + 184)) (hactive : state.halted = false) :
    natRun rom containing 16 state = runOps rom (setCache 1 0) state := by
  let leading := headers ++ setCache 1 0 ++ rawTest (start + 184) ++ rawBody start
  let suffix := boundedTest 1 5 (start + 443) ++ setCache 2 0 ++ boundedTest 2 4 (start + 408) ++
    arguments ++ RawCandidateIncidenceBlock.programAt (start + 305) ++ toolTail start ++ rowTail start
  have hlayout : programAt start = leading ++ setCache 1 0 ++ suffix := by
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 184 := by
    simp only [leading, List.length_append, headers_length, setCache_length, rawTest_length, rawBody_length]
  exact run_straight_layout rom containing start hbound hcode leading (setCache 1 0) suffix 184 hlayout hp
    (by simp [setCache, storeCache, RawCandidateWorkspaceBaseRAM.program, NoJump]) state hpc hactive

theorem run_nodeTest (state : NatState) (hpc : state.pc = 5 * (start + 200)) (hactive : state.halted = false) :
    natRun rom containing 20 state = runOps rom (boundedTest 1 5 (start + 443)) state := by
  let leading := headers ++ setCache 1 0 ++ rawTest (start + 184) ++ rawBody start ++ setCache 1 0
  let suffix := setCache 2 0 ++ boundedTest 2 4 (start + 408) ++ arguments ++
    RawCandidateIncidenceBlock.programAt (start + 305) ++ toolTail start ++ rowTail start
  let lead := loadCache .total 1 ++ loadCell .old 5 ++
    [.base (.subtract .flag .old .total), .base (.base (.constant .index (5 * (start + 443))))]
  have hlead : lead ++ [.jumpIfZero .flag .index] = boundedTest 1 5 (start + 443) := by
    simp only [lead, boundedTest, List.append_assoc, List.cons_append, List.nil_append]
  have hlen : lead.length = 19 := by
    simp only [lead, loadCache_length, loadCell, List.length_append, List.length_cons, List.length_nil]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 200 := by
    simp only [leading, List.length_append, headers_length, setCache_length, rawTest_length, rawBody_length]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix (.jumpIfZero .flag .index)
    200 hlayout hp (by simp [lead, loadCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]) state hpc hactive
  simpa only [hlen, hlead] using hh

theorem run_toolInit (state : NatState) (hpc : state.pc = 5 * (start + 220)) (hactive : state.halted = false) :
    natRun rom containing 16 state = runOps rom (setCache 2 0) state := by
  let leading := headers ++ setCache 1 0 ++ rawTest (start + 184) ++ rawBody start ++ setCache 1 0 ++
    boundedTest 1 5 (start + 443)
  let suffix := boundedTest 2 4 (start + 408) ++ arguments ++
    RawCandidateIncidenceBlock.programAt (start + 305) ++ toolTail start ++ rowTail start
  have hlayout : programAt start = leading ++ setCache 2 0 ++ suffix := by
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 220 := by
    simp only [leading, List.length_append, headers_length, setCache_length, rawTest_length, rawBody_length, boundedTest_length]
  exact run_straight_layout rom containing start hbound hcode leading (setCache 2 0) suffix 220 hlayout hp
    (by simp [setCache, storeCache, RawCandidateWorkspaceBaseRAM.program, NoJump]) state hpc hactive

theorem run_toolTest (state : NatState) (hpc : state.pc = 5 * (start + 236)) (hactive : state.halted = false) :
    natRun rom containing 20 state = runOps rom (boundedTest 2 4 (start + 408)) state := by
  let leading := headers ++ setCache 1 0 ++ rawTest (start + 184) ++ rawBody start ++ setCache 1 0 ++
    boundedTest 1 5 (start + 443) ++ setCache 2 0
  let suffix := arguments ++ RawCandidateIncidenceBlock.programAt (start + 305) ++ toolTail start ++ rowTail start
  let lead := loadCache .total 2 ++ loadCell .old 4 ++
    [.base (.subtract .flag .old .total), .base (.base (.constant .index (5 * (start + 408))))]
  have hlead : lead ++ [.jumpIfZero .flag .index] = boundedTest 2 4 (start + 408) := by
    simp only [lead, boundedTest, List.append_assoc, List.cons_append, List.nil_append]
  have hlen : lead.length = 19 := by
    simp only [lead, loadCache_length, loadCell, List.length_append, List.length_cons, List.length_nil]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ suffix := by
    rw [hlead]
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 236 := by
    simp only [leading, List.length_append, headers_length, setCache_length, rawTest_length, rawBody_length, boundedTest_length]
  have hh := run_branch_layout rom containing start hbound hcode leading lead suffix (.jumpIfZero .flag .index)
    236 hlayout hp (by simp [lead, loadCache, RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]) state hpc hactive
  simpa only [hlen, hlead] using hh

theorem run_arguments (state : NatState) (hpc : state.pc = 5 * (start + 256)) (hactive : state.halted = false) :
    natRun rom containing 49 state = runOps rom arguments state := by
  let leading := headers ++ setCache 1 0 ++ rawTest (start + 184) ++ rawBody start ++ setCache 1 0 ++
    boundedTest 1 5 (start + 443) ++ setCache 2 0 ++ boundedTest 2 4 (start + 408)
  let suffix := RawCandidateIncidenceBlock.programAt (start + 305) ++ toolTail start ++ rowTail start
  have hlayout : programAt start = leading ++ arguments ++ suffix := by
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 256 := by
    simp only [leading, List.length_append, headers_length, setCache_length, rawTest_length, rawBody_length, boundedTest_length]
  exact run_straight_layout rom containing start hbound hcode leading arguments suffix 256 hlayout hp
    (by simp [arguments, readOrd, loadCache, RawCandidateWorkspaceBaseRAM.program, NoJump]) state hpc hactive

theorem run_toolTail (state : NatState) (hpc : state.pc = 5 * (start + 337)) (hactive : state.halted = false) :
    natRun rom containing 71 state = runOps rom (toolTail start) state := by
  let leading := headers ++ setCache 1 0 ++ rawTest (start + 184) ++ rawBody start ++ setCache 1 0 ++
    boundedTest 1 5 (start + 443) ++ setCache 2 0 ++ boundedTest 2 4 (start + 408) ++ arguments ++
    RawCandidateIncidenceBlock.programAt (start + 305)
  let lead := writeNode ++ incrementCache 2 ++ (jumpTo (start + 236)).take 2
  have hlead : lead ++ [.jumpIfZero .flag .index] = toolTail start := by
    simp only [lead, toolTail, jumpTo, List.take_succ_cons, List.take_zero,
      List.append_assoc, List.cons_append, List.nil_append]
  have hlen : lead.length = 70 := by
    simp only [lead, writeNode_length, incrementCache_length, jumpTo, List.take_succ_cons, List.take_zero,
      List.length_append, List.length_cons, List.length_nil]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ rowTail start := by
    rw [hlead]
    simp only [programAt, leading, List.append_assoc]
  have hp : leading.length = 337 := by
    simp only [leading, List.length_append, headers_length, setCache_length, rawTest_length, rawBody_length,
      boundedTest_length, arguments_length, RawCandidateIncidenceBlock.programAt_length]
  have hh := run_branch_layout rom containing start hbound hcode leading lead (rowTail start) (.jumpIfZero .flag .index)
    337 hlayout hp
    (by simp [lead, writeNode, incrementCache, loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program, jumpTo, NoJump])
    state hpc hactive
  simpa only [hlen, hlead] using hh

theorem run_rowTail (state : NatState) (hpc : state.pc = 5 * (start + 408)) (hactive : state.halted = false) :
    natRun rom containing 35 state = runOps rom (rowTail start) state := by
  let leading := headers ++ setCache 1 0 ++ rawTest (start + 184) ++ rawBody start ++ setCache 1 0 ++
    boundedTest 1 5 (start + 443) ++ setCache 2 0 ++ boundedTest 2 4 (start + 408) ++ arguments ++
    RawCandidateIncidenceBlock.programAt (start + 305) ++ toolTail start
  let lead := incrementCache 1 ++ (jumpTo (start + 200)).take 2
  have hlead : lead ++ [.jumpIfZero .flag .index] = rowTail start := by
    simp only [lead, rowTail, jumpTo, List.take_succ_cons, List.take_zero,
      List.append_assoc, List.cons_append, List.nil_append]
  have hlen : lead.length = 34 := by
    simp only [lead, incrementCache_length, jumpTo, List.take_succ_cons, List.take_zero,
      List.length_append, List.length_cons, List.length_nil]
  have hlayout : programAt start = leading ++ (lead ++ [.jumpIfZero .flag .index]) ++ [] := by
    rw [hlead]
    simp only [programAt, leading, List.append_assoc, List.append_nil]
  have hp : leading.length = 408 := by
    simp only [leading, List.length_append, headers_length, setCache_length, rawTest_length, rawBody_length,
      boundedTest_length, arguments_length, RawCandidateIncidenceBlock.programAt_length, toolTail_length]
  have hh := run_branch_layout rom containing start hbound hcode leading lead [] (.jumpIfZero .flag .index)
    408 hlayout hp
    (by simp [lead, incrementCache, loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program, jumpTo, NoJump])
    state hpc hactive
  simpa only [hlen, hlead] using hh

end Containing

theorem query_call (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 443 ≤ containing.length)
    (hcode : ∀ position < 443, containing.getD (start + position) paddingOp =
      (programAt start).getD position paddingOp)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * (start + 305)) (hactive : state.halted = false)
    (hc : state.register .old = candidate.val) (ht : state.register .fresh = tool.val) :
    RawCandidateIncidenceBlock.ReturnedActive (start + 305) state
      (natRun (rawIncidenceROM q full) containing
        (RawCandidateIncidenceRAM.querySteps full.length candidate.val tool.val - 1) state)
      (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
  let leading := headers ++ setCache 1 0 ++ rawTest (start + 184) ++ rawBody start ++ setCache 1 0 ++
    boundedTest 1 5 (start + 443) ++ setCache 2 0 ++ boundedTest 2 4 (start + 408) ++ arguments
  let suffix := toolTail start ++ rowTail start
  have hlayout : programAt start = leading ++ RawCandidateIncidenceBlock.programAt (start + 305) ++ suffix := by
    simp only [programAt, leading, suffix, List.append_assoc]
  have hp : leading.length = 305 := by
    simp only [leading, List.length_append, headers_length, setCache_length, rawTest_length,
      rawBody_length, boundedTest_length, arguments_length]
  apply RawCandidateIncidenceBlock.query q full containing (start + 305) (by omega) ?_
    candidate tool state hpc hactive hc ht
  intro position hposition
  have hh := hcode (305 + position) (by omega)
  have hm := getD_middle leading (RawCandidateIncidenceBlock.programAt (start + 305)) suffix
    position (by rw [RawCandidateIncidenceBlock.programAt_length]; exact hposition)
  rw [← hlayout, hp] at hm
  have hmatch : containing.getD ((start + 305) + position) paddingOp =
      (RawCandidateIncidenceBlock.programAt (start + 305)).getD position paddingOp := by
    simpa only [Nat.add_assoc] using hh.trans hm
  rw [List.getD_eq_getElem containing paddingOp (by omega),
    List.getD_eq_getElem _ paddingOp (by rw [RawCandidateIncidenceBlock.programAt_length]; exact hposition)] at hmatch
  exact hmatch

def AboveFrame (N q bound : Nat) (before after : NatState) : Prop :=
  ∀ address, bound ≤ address → address ≠ workspaceBase N q + 1 →
    address ≠ workspaceBase N q + 2 → address ≠ workspaceBase N q + 3 →
      after.heap address = before.heap address

theorem AboveFrame.refl (N q bound : Nat) (state : NatState) : AboveFrame N q bound state state :=
  fun _ _ _ _ _ => rfl

theorem AboveFrame.trans (N q bound : Nat) {one two three : NatState}
    (h12 : AboveFrame N q bound one two) (h23 : AboveFrame N q bound two three) :
    AboveFrame N q bound one three := by
  intro address hbound h1 h2 h3
  exact (h23 address hbound h1 h2 h3).trans (h12 address hbound h1 h2 h3)

theorem InputSpec.of_aboveFrame (q : Nat) (full : List (Finset (Fin q))) (bound : Nat)
    {before after : NatState} (hspec : InputSpec q full before)
    (hbound : bound ≤ workspaceBase full.length q) (hframe : AboveFrame full.length q bound before after) :
    InputSpec q full after := by
  have hnode : after.heap (nodeCountAddress full.length q) = before.heap (nodeCountAddress full.length q) :=
    hframe _ (by unfold nodeCountAddress; omega) (by unfold nodeCountAddress; omega)
      (by unfold nodeCountAddress; omega) (by unfold nodeCountAddress; omega)
  have hord (node : Nat) : after.heap (ordAddress full.length q node) = before.heap (ordAddress full.length q node) :=
    hframe _ (by unfold ordAddress; omega) (by unfold ordAddress; omega)
      (by unfold ordAddress; omega) (by unfold ordAddress; omega)
  constructor
  · exact hnode.trans hspec.node_count
  · intro node hn
    rw [hord]
    exact hspec.ord_legal node hn
  · intro node hn
    rw [hord]
    exact hspec.ord_support node hn

theorem headers_aboveFrame (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    AboveFrame full.length q 6 state (runOps (rawIncidenceROM q full) headers state) := by
  intro address hbound _h1 _h2 h3
  rw [headers_heap]
  simp [headerHeap, h3, show address ≠ 0 by omega, show address ≠ 1 by omega,
    show address ≠ 2 by omega, show address ≠ 3 by omega, show address ≠ 4 by omega, show address ≠ 5 by omega]

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputRAM
