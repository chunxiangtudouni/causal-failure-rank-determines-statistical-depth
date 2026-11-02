module

public import Paid.RootD27Core_RetainedLayout_035
public import Paid.RootD27Core_EmitLoop_005
public import Paid.RootD27Core_RawSplice_015
public import Paid.PDCompute_SolverStandaloneCode_148

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (HeapList linearExecute)

def priceSlot (upper : Bool) : ℕ:=if upper then 15 else 14
def lengthSlot (upper : Bool) : ℕ:=if upper then 23 else 22
def bufferBase (n k M : ℕ) (upper : Bool) : ℕ:=RootD27.Core.retainedTableBase (99+2*M) n k upper

def PreparedDimensions (before : State) (n k M : ℕ) : Prop:=
  HeapList before 0 [.natural n] ∧ HeapList before 1 [.natural k] ∧ HeapList before 7 [.natural M]

/-- Physical runtime facts to be discharged by Root's real SearchStateRep.
No table or encoded answer occurs in the program below. -/
def SolvePayload (before : State) (n k M : ℕ) (upper : Bool) (solution : MultiplierSolve) : Prop:=
  HeapList before (priceSlot upper) [.rational solution.multiplier] ∧
  HeapList before (lengthSlot upper) [.natural (encodeTable solution.table).length] ∧
  HeapList before (bufferBase n k M upper) (encodeTable solution.table)

def StatePayload (before : State) (n k M : ℕ) : MultiplierState→Prop
  | .exact solution => HeapList before 13 [.natural 0] ∧ SolvePayload before n k M false solution
  | .bracket lower upper => HeapList before 13 [.natural 1] ∧
      SolvePayload before n k M false lower ∧ SolvePayload before n k M true upper

def outputSlotCode (slot : ℕ) : List Instruction:=
  [.constant .address (.natural slot),.load .value .address,.output .value]

/-- Runtime n/k/M and true length are read from actual live heap cells.
Only fixed addresses and literal62/70,2,99 occur in the code. -/
def pointerCode (upper : Bool) : List Instruction:=
  [.constant .address (.natural 0),.load .index .address,
   .constant .flag (.natural 1),.natOp .add .index .index .flag,
   .constant .address (.natural 1),.load .value .address,
   .natOp .add .value .value .flag,.natOp .multiply .index .index .value,
   .constant .value (.natural (if upper then 70 else 62)),.natOp .multiply .total .index .value,
   .constant .address (.natural 7),.load .value .address,
   .constant .flag (.natural 2),.natOp .multiply .value .value .flag,
   .constant .flag (.natural 99),.natOp .add .value .value .flag,
   .natOp .add .total .total .value,
   .constant .address (.natural (lengthSlot upper)),.load .index .address,
   .constant .flag (.natural 0),.natOp .add .address .total .flag]

def pointerResult (before : State) (n k M count : ℕ) (upper : Bool) : State:=
  {before with
    register:=Function.update (Function.update (Function.update (Function.update (Function.update before.register
      .index (.natural count)) .value (.natural (99+2*M))) .total (.natural (bufferBase n k M upper)))
      .flag (.natural 0)) .address (.natural (bufferBase n k M upper))
    pc:=before.pc+21}

def solveCode (origin : ℕ) (upper : Bool) (returnPC : ℕ) : List Instruction:=
  outputSlotCode (priceSlot upper)++pointerCode upper++RootD27.Core.emitHeapCode (origin+24) returnPC

def stateGuardCode (upperPC returnPC : ℕ) : List Instruction:=
  [.constant .address (.natural 13),.load .index .address,.branchZero .index returnPC upperPC]

/-- A fixed68-op state output block. Real tag13 determines the actual
branch, and both prices and entire original tables are physically read. -/
def stateCode (origin returnPC : ℕ) : List Instruction:=
  outputSlotCode 13++solveCode (origin+3) false (origin+34)++
    stateGuardCode (origin+37) returnPC++solveCode (origin+37) true returnPC

theorem outputSlot_length (slot : ℕ) : (outputSlotCode slot).length=3:=rfl
theorem pointer_length (upper : Bool) : (pointerCode upper).length=21:=rfl
theorem solve_length (origin : ℕ) (upper : Bool) (returnPC : ℕ) : (solveCode origin upper returnPC).length=31:=rfl
theorem stateGuard_length (upperPC returnPC : ℕ) : (stateGuardCode upperPC returnPC).length=3:=rfl
theorem state_length (origin returnPC : ℕ) : (stateCode origin returnPC).length=68:=rfl

end PDCompute.CoreEmit
