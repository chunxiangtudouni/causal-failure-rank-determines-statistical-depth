module

public import Paid.PDCompute_SolverCellProgram_112

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation

/-- Complete fixed nested row/tool loop, including row0 and all columns
0..k. Original n/k remain actual saved Header3/4 values; neither program
length nor code generation depends on them or on input rationals. -/
def matrixCode (mode : ReaderMode) (origin : ℕ) : List Instruction :=
  let initializeRow:=headerCode [.constant 19 (.natural 0)]
  let initializeColumn:=headerCode [.constant 20 (.natural 0)]
  let rowTest:=origin+initializeRow.length
  let columnInit:=rowTest+8
  let columnTest:=columnInit+initializeColumn.length
  let cellOrigin:=columnTest+8
  let cell:=fullCellCode mode cellOrigin
  let columnAdvance:=addNatSlot 20 1
  let rowAdvance:=addNatSlot 19 1
  let rowAdvancePC:=cellOrigin+cell.length+columnAdvance.length+1
  let finish:=rowAdvancePC+rowAdvance.length+1
  initializeRow++naturalBranchCode .lessEqual 19 3 finish columnInit++initializeColumn++
    naturalBranchCode .lessEqual 20 4 rowAdvancePC cellOrigin++cell++columnAdvance++[.jump columnTest]++
    rowAdvance++[.jump rowTest]

end PDCompute.Solver
