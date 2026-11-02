module

public import Structure.PA06_A19Prepare_ControlBank017_Geometry
public import PaperProofs.Structure.RawCandidateChildrenPrefix
public import PaperProofs.Structure.RawCandidateChildrenLayout
public import PaperProofs.Structure.PA17_UniformGenerator_035g
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled fixed children-cache producer, preserving hardware.address.
The body scans parent and child IDs in ascending order. Only small literal
control offsets and compile positions occur in code; N/q/t/P/CB never do.
This file currently certifies the concrete blocks. Whole nested-loop
simulation and the prepared-tree entry discharge are separate obligations. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawCandidateChildrenLayout RawCandidateChildrenPrefix

def degreeBase (CB M : Nat) : Nat := CB + 533 + 5 * M
def childrenBase (CB M t : Nat) : Nat := degreeBase CB M + t
def parentAddress (CB M child : Nat) : Nat := CB + 533 + 4 * M + child

def loadRel (target : Register) (offset : Nat) : List PackingOp :=
  [.base (.base (.constant .index offset)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap target .index))]
def storeRel (source : Register) (offset : Nat) : List PackingOp :=
  [.base (.base (.constant .index offset)), .base (.base (.add .index .address .index)),
   .base (.base (.storeHeap .index source))]
def setRel (offset value : Nat) : List PackingOp :=
  [.base (.base (.constant .value value))] ++ storeRel .value offset
def incrementRel (offset : Nat) : List PackingOp :=
  loadRel .value offset ++ [.base (.base (.constant .total 1)), .base (.base (.add .value .value .total))] ++
    storeRel .value offset

/-- CB+528 stores the actually copied source heap16=M. The true cached t is
CB+532+4M, not an argument supplied to the generated program. -/
def initializeCache : List PackingOp :=
  loadRel .total 528 ++
    [.base (.base (.constant .index 4)), .arithmetic .multiply .index .total .index,
     .base (.base (.constant .value 532)), .base (.base (.add .index .index .value)),
     .base (.base (.add .index .address .index)), .base (.base (.loadHeap .value .index))] ++
    storeRel .value 70 ++
    [.base (.base (.constant .index 5)), .arithmetic .multiply .total .total .index,
     .base (.base (.constant .fresh 533)), .base (.base (.add .fresh .fresh .total)),
     .base (.base (.add .fresh .address .fresh))] ++ storeRel .fresh 67 ++
    [.base (.base (.add .fresh .fresh .value))] ++ storeRel .fresh 68 ++ setRel 64 0 ++ setRel 66 0

def initializeRow : List PackingOp := setRel 65 0 ++ setRel 69 0

def boundedTest (counter exit : Nat) : List PackingOp :=
  loadRel .value 70 ++ loadRel .total counter ++
    [.base (.subtract .flag .value .total), .base (.base (.constant .index (5 * exit))),
     .jumpIfZero .flag .index]

def loadParent : List PackingOp :=
  loadRel .old 65 ++ loadRel .total 528 ++
    [.base (.base (.constant .index 4)), .arithmetic .multiply .total .total .index,
     .base (.base (.constant .index 533)), .base (.base (.add .index .index .total)),
     .base (.base (.add .index .index .old)), .base (.base (.add .index .address .index)),
     .base (.base (.loadHeap .value .index))]

def matchLead (start : Nat) : List PackingOp :=
  loadParent ++ loadRel .old 64 ++
    [.base (.base (.constant .total 1)), .base (.base (.add .old .old .total)),
     .base (.subtract .flag .value .old), .base (.subtract .total .old .value),
     .base (.base (.add .flag .flag .total)), .base (.base (.constant .index (5 * (start + 84))))]
def matchTest (start : Nat) : List PackingOp := matchLead start ++ [.jumpIfZero .flag .index]

def writeChild : List PackingOp :=
  loadRel .fresh 65 ++ loadRel .old 68 ++ loadRel .total 66 ++
    [.base (.base (.add .index .old .total)), .base (.base (.storeHeap .index .fresh))]
def matched : List PackingOp := writeChild ++ incrementRel 69 ++ incrementRel 66

def innerLead (start : Nat) : List PackingOp := incrementRel 65 ++ (jumpTo (start + 49)).take 2
def innerTail (start : Nat) : List PackingOp := innerLead start ++ [.jumpIfZero .flag .index]

def writeDegree : List PackingOp :=
  loadRel .value 69 ++ loadRel .old 64 ++ loadRel .total 67 ++
    [.base (.base (.add .index .old .total)), .base (.base (.storeHeap .index .value))]
def outerLead (start : Nat) : List PackingOp :=
  writeDegree ++ incrementRel 64 ++ (jumpTo (start + 32)).take 2
def outerTail (start : Nat) : List PackingOp := outerLead start ++ [.jumpIfZero .flag .index]

def programAt (start : Nat) : List PackingOp :=
  initializeCache ++ boundedTest 64 (start + 144) ++ initializeRow ++ boundedTest 65 (start + 122) ++
    matchTest start ++ jumpTo (start + 111) ++ matched ++ innerTail start ++ outerTail start

theorem loadRel_length (target : Register) (offset : Nat) : (loadRel target offset).length = 3 := rfl
theorem storeRel_length (source : Register) (offset : Nat) : (storeRel source offset).length = 3 := rfl
theorem setRel_length (offset value : Nat) : (setRel offset value).length = 4 := rfl
theorem incrementRel_length (offset : Nat) : (incrementRel offset).length = 8 := rfl
theorem initializeCache_length : initializeCache.length = 32 := rfl
theorem initializeRow_length : initializeRow.length = 8 := rfl
theorem boundedTest_length (counter exit : Nat) : (boundedTest counter exit).length = 9 := rfl
theorem loadParent_length : loadParent.length = 13 := rfl
theorem matchLead_length (start : Nat) : (matchLead start).length = 22 := rfl
theorem matchTest_length (start : Nat) : (matchTest start).length = 23 := rfl
theorem writeChild_length : writeChild.length = 11 := rfl
theorem matched_length : matched.length = 27 := rfl
theorem innerTail_length (start : Nat) : (innerTail start).length = 11 := rfl
theorem outerTail_length (start : Nat) : (outerTail start).length = 22 := rfl
theorem programAt_length (start : Nat) : (programAt start).length = 144 := rfl

theorem loadRel_value (rom : PhysicalROM) (target : Register) (offset : Nat) (state : NatState) :
    (runOps rom (loadRel target offset) state).register target = state.heap (state.register .address + offset) := by
  cases target <;> rfl

theorem loadRel_address (rom : PhysicalROM) (target : Register) (offset : Nat) (state : NatState)
    (ht : target ≠ .address) :
    (runOps rom (loadRel target offset) state).register .address = state.register .address := by
  cases target <;> simp_all [loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem loadRel_heap (rom : PhysicalROM) (target : Register) (offset : Nat) (state : NatState) :
    (runOps rom (loadRel target offset) state).heap = state.heap := rfl

theorem storeRel_heap (rom : PhysicalROM) (source : Register) (offset : Nat) (state : NatState)
    (hs : source ≠ .index) :
    (runOps rom (storeRel source offset) state).heap =
      Function.update state.heap (state.register .address + offset) (state.register source) := by
  cases source <;> simp_all [storeRel, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem storeRel_address (rom : PhysicalROM) (source : Register) (offset : Nat) (state : NatState) :
    (runOps rom (storeRel source offset) state).register .address = state.register .address := rfl

theorem setRel_heap (rom : PhysicalROM) (offset value : Nat) (state : NatState) :
    (runOps rom (setRel offset value) state).heap = Function.update state.heap (state.register .address + offset) value := rfl

theorem incrementRel_heap (rom : PhysicalROM) (offset : Nat) (state : NatState) :
    (runOps rom (incrementRel offset) state).heap =
      Function.update state.heap (state.register .address + offset) (state.heap (state.register .address + offset) + 1) := rfl

theorem loadParent_value (rom : PhysicalROM) (CB M child : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hM : state.heap (CB + 528) = M) (hc : state.heap (CB + 65) = child) :
    (runOps rom loadParent state).register .value = state.heap (parentAddress CB M child) := by
  simp [loadParent, loadRel, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    hCB, hM, hc, parentAddress, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

theorem loadParent_heap (rom : PhysicalROM) (state : NatState) : (runOps rom loadParent state).heap = state.heap := rfl

theorem loadParent_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom loadParent state).register .address = state.register .address := rfl

theorem writeChild_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom writeChild state).heap =
      Function.update state.heap (state.heap (state.register .address + 68) + state.heap (state.register .address + 66))
        (state.heap (state.register .address + 65)) := rfl

theorem writeDegree_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom writeDegree state).heap =
      Function.update state.heap (state.heap (state.register .address + 64) + state.heap (state.register .address + 67))
        (state.heap (state.register .address + 69)) := rfl

/-- The fixed initializer really computes both dynamic output pointers and
loads t from the copied node-count address; it never embeds an input size. -/
theorem initializeCache_heap (rom : PhysicalROM) (CB M t : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hM : state.heap (CB + 528) = M)
    (ht : state.heap (CB + 532 + 4 * M) = t) :
    (runOps rom initializeCache state).heap =
      Function.update (Function.update (Function.update (Function.update (Function.update state.heap
        (CB + 70) t) (CB + 67) (degreeBase CB M)) (CB + 68) (childrenBase CB M t))
          (CB + 64) 0) (CB + 66) 0 := by
  have he : CB + (M * 4 + 532) = CB + 532 + 4 * M := by omega
  have ht' : state.heap (CB + (M * 4 + 532)) = t := (congrArg state.heap he).trans ht
  simp [initializeCache, loadRel, storeRel, setRel, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, hCB, hM, ht', degreeBase, childrenBase,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

theorem initializeCache_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom initializeCache state).register .address = state.register .address := rfl

theorem branch_pc (rom : PhysicalROM) (CB size count counter exit : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hs : state.heap (CB + 70) = size)
    (hc : state.heap (CB + counter) = count) :
    (runOps rom (boundedTest counter exit) state).pc =
      if size - count = 0 then 5 * exit else state.pc + 45 := by
  simp [boundedTest, loadRel, runOps, natExecuteOp, Op.execute, Instruction.execute,
    hCB, hs, hc, Nat.add_assoc]

theorem match_pc (rom : PhysicalROM) (CB M parent child start : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hM : state.heap (CB + 528) = M)
    (hp : state.heap (CB + 64) = parent) (hc : state.heap (CB + 65) = child) :
    (runOps rom (matchTest start) state).pc =
      if state.heap (parentAddress CB M child) = parent + 1 then 5 * (start + 84) else state.pc + 115 := by
  simp [matchTest, matchLead, loadParent, loadRel, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, hCB, hM, hp, hc, parentAddress,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  split_ifs <;> omega

theorem initializeRow_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom initializeRow state).heap =
      Function.update (Function.update state.heap (state.register .address + 65) 0)
        (state.register .address + 69) 0 := rfl

theorem initializeRow_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom initializeRow state).register .address = state.register .address := rfl

theorem boundedTest_heap (rom : PhysicalROM) (counter exit : Nat) (state : NatState) :
    (runOps rom (boundedTest counter exit) state).heap = state.heap := rfl

theorem boundedTest_address (rom : PhysicalROM) (counter exit : Nat) (state : NatState) :
    (runOps rom (boundedTest counter exit) state).register .address = state.register .address := rfl

theorem matchTest_heap (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (matchTest start) state).heap = state.heap := rfl

theorem matchTest_address (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (matchTest start) state).register .address = state.register .address := rfl

/-- The real matched stores, protected against accidental output/control
aliasing by the actual stored child-array pointer. -/
theorem matched_heap (rom : PhysicalROM) (CB : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hptr : CB + 71 ≤ state.heap (CB + 68)) :
    (runOps rom matched state).heap =
      Function.update (Function.update (Function.update state.heap
        (state.heap (CB + 68) + state.heap (CB + 66)) (state.heap (CB + 65)))
          (CB + 69) (state.heap (CB + 69) + 1)) (CB + 66) (state.heap (CB + 66) + 1) := by
  simp (disch := omega) [matched, writeChild, incrementRel, loadRel, storeRel, runOps,
    natExecuteOp, Op.execute, Instruction.execute, hCB, Function.update_apply]

theorem matched_address (rom : PhysicalROM) (state : NatState) :
    (runOps rom matched state).register .address = state.register .address := rfl

theorem innerTail_heap (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (innerTail start) state).heap =
      Function.update state.heap (state.register .address + 65) (state.heap (state.register .address + 65) + 1) := rfl

theorem innerTail_pc (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (innerTail start) state).pc = 5 * (start + 49) := by
  simp [innerTail, innerLead, incrementRel, loadRel, storeRel, jumpTo,
    runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem innerTail_address (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (innerTail start) state).register .address = state.register .address := rfl

theorem outerTail_heap (rom : PhysicalROM) (CB start : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hptr : CB + 71 ≤ state.heap (CB + 67)) :
    (runOps rom (outerTail start) state).heap =
      Function.update (Function.update state.heap (state.heap (CB + 64) + state.heap (CB + 67))
        (state.heap (CB + 69))) (CB + 64) (state.heap (CB + 64) + 1) := by
  simp (disch := omega) [outerTail, outerLead, writeDegree, incrementRel, loadRel, storeRel, jumpTo,
    runOps, natExecuteOp, Op.execute, Instruction.execute, hCB, Function.update_apply]

theorem outerTail_pc (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (outerTail start) state).pc = 5 * (start + 32) := by
  simp [outerTail, outerLead, writeDegree, incrementRel, loadRel, storeRel, jumpTo,
    runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem outerTail_address (rom : PhysicalROM) (start : Nat) (state : NatState) :
    (runOps rom (outerTail start) state).register .address = state.register .address := rfl

/-- The proposed arrays and their final end are genuinely inside the SAME
original control-bank cache allowance. The tree degree+edge size is linear. -/
theorem output_room (CB M t : Nat) (ht : t ≤ M) :
    childrenBase CB M t + (t - 1) ≤ CB + 512 + (16 + 8 * M + 8192) := by
  unfold childrenBase degreeBase
  omega

/-- Conservative real branch-step bound once loop induction is connected. -/
def iterationSteps (words : Nat → Nat) (parent child : Nat) : Nat :=
  if words child = parent + 1 then 70 else 46

theorem iterationSteps_le (words : Nat → Nat) (parent child : Nat) : iterationSteps words parent child ≤ 70 := by
  unfold iterationSteps
  split_ifs <;> omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
