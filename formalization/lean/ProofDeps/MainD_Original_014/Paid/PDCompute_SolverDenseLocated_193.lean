module

public import Paid.PDCompute_SolverDenseCallee_192
public import Paid.PDCompute_SolverLocated_147
public import Paid.PDLower_CalibrationCompute_CallerEmbedding_073

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame

attribute [local irreducible] fullCellCode matrixCode matrixPackCode solverCalleeCode

/-- Same REAL complete callee witness, with proper-prefix PC scope
DERIVED from its actual successful chain in the literal located block.
This adds no scope oracle and performs no replacement-label counting. -/
theorem solver_callee_dense_located (mode : ReaderMode) (input : List Cell) (origin : ℕ)
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source returnPC : ℕ)
    (hpc : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (old : before.register .old=.natural returnPC) (address : before.register .address=.natural source)
    (total : before.register .total=.rational penalty) (index : before.register .index=.natural n)
    (value : before.register .value=.natural k) (flag : before.register .flag=.rational fee)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step (solverLocatedProgram mode origin) input first=some later) ∧
      time (solverLocatedProgram mode origin) trace ≤ 38000*(P.certificate.M+1)*entryCount n k ∧
      Return P fee penalty n k base returnPC before after ∧
      (∀ state∈trace,RegionMemory before state (workspace base n k)) ∧
      peakCells trace ≤ workingCells before+62*entryCount n k ∧
      (∀ state∈trace.dropLast,origin ≤ state.pc ∧ state.pc < origin+(solverCalleeCode mode origin).length) ∧
      DenseOriginalTable after P fee penalty base n k ∧
      PDLower.CalibrationCompute.HeapList after (cellBase base k n k)
        (denseEncodeEntry (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) n k)) := by
  obtain ⟨trace,after,head,last,chain,cost,returned,memory,space,dense,root⟩:=solver_callee_dense_trace mode (solverLocatedProgram mode origin) input origin
    (solverLocated_fetch mode origin) P fee penalty before base n k source returnPC hpc fresh old address total index value flag hsource avoids
  refine ⟨trace,after,head,last,chain,cost,returned,memory,space,?_,dense,root⟩
  simpa only [List.size_toArray] using PDLower.CalibrationCompute.located_chain_scope origin (solverCalleeCode mode origin).toArray input trace chain

end PDCompute.Solver
