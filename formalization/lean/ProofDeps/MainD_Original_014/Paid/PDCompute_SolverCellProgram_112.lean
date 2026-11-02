module

public import Paid.PDCompute_SolverScanChoice_105
public import Paid.PDCompute_SolverScanReset_106
public import Paid.PDCompute_SolverBadChoice_108
public import Paid.PDCompute_SolverRowPointerSetup_087
public import Paid.PDCompute_SolverGoodBranchRuntime_091

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation

/-- All original endpoint and entry values are read at runtime. The
code generator accepts only static reader mode and its absolute origin. -/
def nonzeroCellFieldsCode (mode : ReaderMode) (origin : ℕ) : List Instruction :=
  let good:=goodEntryObjectiveCode
  let zero:=headerCode [.constant 46 (.natural 0)]
  let badOrigin:=origin+good.length+zero.length
  let bad:=badChoiceCode badOrigin
  let reset:=runtimeCode scanResetCommands
  let scanOrigin:=badOrigin+bad.length+reset.length
  good++zero++bad++reset++scanChoiceCode mode scanOrigin

def positiveCellFieldsCode (mode : ReaderMode) (origin : ℕ) : List Instruction :=
  let zero:=headerCode [.constant 46 (.rational 0)]
  zero++choiceCode (rationalBranchCode .equal 2 46)
    (fun _ => headerCode (terminalFieldsCommands true)) (nonzeroCellFieldsCode mode) (origin+zero.length)

/-- Both row-zero and positive-row paths really occur in the same
program. The row-zero block contains the actual pointer correction. -/
def cellFieldsCode (mode : ReaderMode) (origin : ℕ) : List Instruction :=
  let zero:=headerCode [.constant 46 (.natural 0)]
  zero++choiceCode (naturalBranchCode .equal 19 46)
    (fun _ => headerCode finishRowFieldsCommands) (positiveCellFieldsCode mode) (origin+zero.length)

def fullCellCode (mode : ReaderMode) (origin : ℕ) : List Instruction :=
  rowPointerSetupCode++cellFieldsCode mode (origin+rowPointerSetupCode.length)++writeCurrentEntryCode

end PDCompute.Solver
