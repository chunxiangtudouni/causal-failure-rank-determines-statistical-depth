module
public import Paid.PDCompute_Nat_SelectedPointerOriginal_019

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

/-- Actual original register entry chooses the ONE additive caller budget
for all original natural phases. This packet also exports the exact actual
pointer/store47, row0copy, branch/guard, initialization and row/column
increment/backedge certificates; rational matrix/scan assembly stays with
the parent solver line. The entry trace ends at the real matrix start. -/
theorem solver_natural_entry (mode : ReaderMode) (origin : ℕ) (input : List Cell)
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source returnPC : ℕ)
    (hpc : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (old : before.register .old=.natural returnPC) (address : before.register .address=.natural source)
    (total : before.register .total=.rational penalty) (index : before.register .index=.natural n)
    (value : before.register .value=.natural k) (flag : before.register .flag=.rational fee)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k) :
    ∃ trace : List State,∃ ready : State,∃ values : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some ready ∧
      trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧ time (solverLocatedProgram mode origin) trace≤2610 ∧
      Header ready base values ∧ values 0=.natural source ∧ values 1=.natural returnPC ∧ values 2=.rational penalty ∧
      values 3=.natural n ∧ values 4=.natural k ∧ values 5=.rational fee ∧ values 6=.natural P.certificate.M ∧
      ready.register .fresh=.natural base ∧ ready.pc=origin+46 ∧ EndpointSource mode input P source ready ∧
      Frame before ready base n k ∧ ready.output=before.output ∧
      peakCells trace≤workingCells before+62*entryCount n k ∧
      peakOperandBits trace≤originalControlBudget (PDCompute.Pack.initialBits before) P fee penalty n k origin (solverCalleeCode mode origin).length ∧
      natBits returnPC≤originalControlBudget (PDCompute.Pack.initialBits before) P fee penalty n k origin (solverCalleeCode mode origin).length ∧
      SolverControlContext before (PDCompute.Pack.initialBits before) base n k mode origin
        (originalControlBudget (PDCompute.Pack.initialBits before) P fee penalty n k origin (solverCalleeCode mode origin).length) ∧
      (∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+(solverCalleeCode mode origin).length) ∧
      ∀ state∈trace,RegionMemory before state (workspace base n k) ∧ RootD27.Bits.SafeBits state
        (originalControlBudget (PDCompute.Pack.initialBits before) P fee penalty n k origin (solverCalleeCode mode origin).length) := by
  obtain ⟨trace,ready,values,head,last,chain,cost,header,v0,v1,v2,v3,v4,v5,v6,freshAfter,pcAfter,sourceAfter,frame,output,space,returnBits,context,resources⟩:=
    solver_natural_entry_resources mode origin input P fee penalty before base n k source returnPC hpc fresh old address total index value flag hsource avoids
  have scope : ∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+(solverCalleeCode mode origin).length:=by
    simpa only [List.size_toArray] using PDLower.CalibrationCompute.located_chain_scope origin (solverCalleeCode mode origin).toArray input trace chain
  have bitBound:=PDCompute.Pack.safeBits_peak trace _ (fun state member=>(resources state member).2)
  exact ⟨trace,ready,values,head,last,chain,cost,header,v0,v1,v2,v3,v4,v5,v6,freshAfter,pcAfter,sourceAfter,frame,output,space,
    bitBound,returnBits,context,scope,resources⟩

end PDCompute.NatControl
