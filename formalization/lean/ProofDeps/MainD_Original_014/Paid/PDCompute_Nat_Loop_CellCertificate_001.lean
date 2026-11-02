module
public import Paid.PDCompute_Nat_Resources_017
public import Paid.PDCompute_SolverMatrixRuntime_130

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.NatLoop
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame PDCompute.NatControl

/-- INTERNAL composition certificate. DP's actual fullcell implementation
constructs this from original code. The final D27 goal must not assume it.
The statement is original119 plus incoming/full SAME-trace SafeBits only;
all original dirty-live, source and n/k quantifiers are retained. -/
def FullCellSameB (mode : ReaderMode) (rootOrigin matrixOrigin : ℕ) (input : List Cell)
    (P : Parameters) (fee penalty : ℚ) (base n k source budget : ℕ) : Prop :=
  ∀ (row column : ℕ) (before : State) (values : ℕ → Cell),
    before.pc=matrixCellPC matrixOrigin→Header before base values→before.register .fresh=.natural base→
    EndpointSource mode input P source before→EndpointAvoids mode P source base n k→
    values 0=.natural source→values 2=.rational penalty→values 4=.natural k→
    values 5=.rational fee→values 6=.natural P.certificate.M→values 19=.natural row→values 20=.natural column→
    row≤n→column≤k→DensePrefix before base k (solverEntry P fee penalty k) (row*(k+1)+column)→
    RootD27.Bits.SafeBits before budget→
    FetchesCode (solverLocatedProgram mode rootOrigin) (matrixCellPC matrixOrigin) (fullCellCode mode (matrixCellPC matrixOrigin))→
    ∃ trace : List State,∃ after : State,∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step (solverLocatedProgram mode rootOrigin) input first=some later) ∧
      time (solverLocatedProgram mode rootOrigin) trace≤2500*(P.certificate.M+1)+23400 ∧ Header after base afterValues ∧
      DensePrefix after base k (solverEntry P fee penalty k) (row*(k+1)+column+1) ∧
      (∀ slot,MatrixInputSlot slot→afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=matrixCellPC matrixOrigin+(fullCellCode mode (matrixCellPC matrixOrigin)).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (cellRegion base headerWords ∪ cellRegion (cellBase base k row column) 6)) ∧
      ∀ state∈trace,RootD27.Bits.SafeBits state budget

end PDCompute.NatLoop
