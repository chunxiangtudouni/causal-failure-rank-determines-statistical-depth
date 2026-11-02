module

public import Paid.RootD27Endpoint_Math_001
public import Paid.PDCompute_SolverHeaderInit_029
public import Paid.PDMenu_ComputeFrame_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver
open PDLower.CalibrationCompute (loadSlot storeSlot)

/-- Save six genuine entry arguments with the frozen sixteen-op prologue.
The remaining forty-two header cells are written by the actual seven-row
padding loop. Its first instruction sets flag=1 itself. -/
def paddingSetup : List Instruction :=
  [.constant .address (.natural 6),.natOp .add .address .fresh .address,
   .constant .index (.natural 7)]

/-- Constants and the odds are generated from saved gamma; no endpoint
or precomputed power is supplied by the caller. Slots0..5 stay unchanged. -/
def initialCommands : List HeaderCommand :=
  [.constant 13 (.rational 1),.constant 14 (.rational 2),
   .constant 8 (.natural 0),.constant 7 (.rational 1),
   .rational .multiply 14 2 12,.rational .add 13 12 15,
   .rational .subtract 13 12 16,.rational .divide 15 16 6]

/-- Actually write the original list length M+1 at E. -/
def cacheHeaderCode : List Instruction :=
  loadSlot 3 .total++
  [.constant .value (.natural 1),.natOp .add .total .total .value]++
  storeSlot 17 .total++loadSlot 0 .address++[.store .address .total]

def initializationCode (origin : ℕ) : List Instruction :=
  solverPrologue++paddingSetup++baseRowCode (origin+19)++
    headerCode initialCommands++cacheHeaderCode

def rowTestCode (bodyPC returnPC : ℕ) : List Instruction :=
  loadSlot 8 .index++loadSlot 3 .total++
  [.natCompare .lessEqual .flag .index .total,.branchZero .flag returnPC bodyPC]

def castRowCode : List Instruction :=
  loadSlot 8 .total++[.natToRat .total .total]++storeSlot 18 .total

/-- Each rational operation expands to ten original scalar instructions.
The original mean/charge formula is used, including m=0. -/
def rowCommands : List HeaderCommand :=
  [.rational .add 13 7 15,.rational .divide 13 15 9,
   .rational .multiply 14 9 16,.rational .subtract 13 16 16,
   .rational .multiply 18 16 18,.rational .divide 18 12 10,
   .rational .multiply 4 10 11]

/-- All loads precede final pointer construction because loadSlot uses
.address as scratch. Saved returnPC remains in slot1 while .old holds
this row's charge. E+1+2m and E+2+2m are actual store addresses. -/
def pairStoreCode : List Instruction :=
  loadSlot 9 .flag++loadSlot 11 .old++loadSlot 8 .index++loadSlot 0 .total++
  [.constant .value (.natural 2),.natOp .multiply .index .index .value,
   .constant .value (.natural 1),.natOp .add .index .index .value,
   .natOp .add .address .total .index,.store .address .flag,
   .natOp .add .address .address .value,.store .address .old]

def advanceCode : List Instruction :=
  headerCode [.rational .multiply 7 6 7]++loadSlot 8 .total++
  [.constant .value (.natural 1),.natOp .add .total .total .value]++storeSlot 8 .total

def rowBodyCode (testPC : ℕ) : List Instruction :=
  castRowCode++headerCode rowCommands++pairStoreCode++advanceCode++[.jump testPC]

/-- Restore actual ABI registers and return through the original indirect
jump instruction. No synthetic final state replaces this operation. -/
def returnCode : List Instruction :=
  loadSlot 1 .old++loadSlot 3 .index++
  [.constant .total (.natural 2),.natOp .multiply .index .index .total,
   .constant .total (.natural 3),.natOp .add .index .index .total]++
  loadSlot 0 .address++[.jumpIndirect .old]

def endpointCode (origin : ℕ) : List Instruction :=
  initializationCode origin++rowTestCode (origin+113) (origin+229)++
    rowBodyCode (origin+105)++returnCode

def endpointProgram (origin : ℕ) : Program := (endpointCode origin).toArray

theorem paddingSetup_length : paddingSetup.length=3 := rfl
theorem initialCommands_length : initialCommands.length=8 := rfl
theorem initialScalar_length : (headerCode initialCommands).length=56 := rfl
theorem cacheHeaderCode_length : cacheHeaderCode.length=12 := rfl
theorem initializationCode_length (origin : ℕ) : (initializationCode origin).length=105 := rfl
theorem rowTestCode_length (bodyPC returnPC : ℕ) : (rowTestCode bodyPC returnPC).length=8 := rfl
theorem castRowCode_length : castRowCode.length=7 := rfl
theorem rowScalarCode_length : (headerCode rowCommands).length=70 := rfl
theorem pairStoreCode_length : pairStoreCode.length=20 := rfl
theorem advanceCode_length : advanceCode.length=18 := rfl
theorem rowBodyCode_length (testPC : ℕ) : (rowBodyCode testPC).length=116 := rfl
theorem returnCode_length : returnCode.length=14 := rfl
theorem endpointCode_length (origin : ℕ) : (endpointCode origin).length=243 := by
  simp only [endpointCode,List.length_append,initializationCode_length,
    rowTestCode_length,rowBodyCode_length,returnCode_length]
theorem endpointProgram_size (origin : ℕ) : (endpointProgram origin).size=243 := by
  simp only [endpointProgram,List.size_toArray,endpointCode_length]

theorem initialization_not_loop_entry (origin : ℕ) : origin≠origin+105 := by omega

end RootD27.Endpoint
