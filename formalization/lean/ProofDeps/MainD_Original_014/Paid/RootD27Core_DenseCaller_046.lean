module

public import Paid.RootD27Core_RawSplice_015
public import Paid.RootD27Core_HeapSolverDispatch_018
public import Paid.PDCompute_SolverDenseLocated_193

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

/-- The ONE complete actual solver witness executes in any containing
program with its genuine literal body. Same readonly input, actual table,
return, every-prefix memory, peak cells and derived PC scope are retained. -/
theorem solver_callee_dense_in_program (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode program origin (solverCalleeCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source returnPC : ℕ)
    (position : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (old : before.register .old=.natural returnPC) (address : before.register .address=.natural source)
    (total : before.register .total=.rational penalty) (index : before.register .index=.natural n)
    (value : before.register .value=.natural k) (flag : before.register .flag=.rational fee)
    (endpoint : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤38000*(P.certificate.M+1)*PDCompute.Solver.entryCount n k+15 ∧
      Return P fee penalty n k base returnPC before after ∧
      (∀ state∈trace,RegionMemory before state (workspace base n k)) ∧
      peakCells trace≤workingCells before+62*PDCompute.Solver.entryCount n k ∧
      (∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+(solverCalleeCode mode origin).length) ∧
      DenseOriginalTable after P fee penalty base n k ∧
      PDLower.CalibrationCompute.HeapList after (cellBase base k n k)
        (denseEncodeEntry (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) n k)) := by
  obtain ⟨trace,after,head,last,chain,cost,returned,memory,peak,scope,dense,root⟩:=
    solver_callee_dense_located mode input origin P fee penalty before base n k source returnPC
      position fresh old address total index value flag endpoint avoids
  have fetched : ∀ state∈trace.dropLast,(solverLocatedProgram mode origin)[state.pc]?=program[state.pc]? := by
    intro state member
    have bounds:=scope state member
    have addressed : origin+(state.pc-origin)=state.pc:=Nat.add_sub_of_le bounds.1
    have offsetBound : state.pc-origin<(solverCalleeCode mode origin).length:=by omega
    calc
      (solverLocatedProgram mode origin)[state.pc]?=
          (solverLocatedProgram mode origin)[origin+(state.pc-origin)]? := by rw [addressed]
      _=(solverCalleeCode mode origin)[state.pc-origin]? := by
        rw [solverLocatedProgram,locatedBlock_fetch,List.getElem?_toArray]
      _=program[origin+(state.pc-origin)]? := (fetch (state.pc-origin) offsetBound).symm
      _=program[state.pc]? := by rw [addressed]
  have callerChain:=chain_same_input_of_fetch _ program input trace fetched chain
  have callerCost:=(time_le_of_dropLast_fetch_eq _ program trace fetched).trans (Nat.add_le_add_right cost 15)
  exact ⟨trace,after,head,last,callerChain,callerCost,returned,memory,peak,scope,dense,root⟩

end RootD27.Core
