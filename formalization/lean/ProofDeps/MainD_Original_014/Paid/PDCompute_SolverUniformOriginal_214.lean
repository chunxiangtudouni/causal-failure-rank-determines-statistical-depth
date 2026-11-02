module

public import Paid.PDCompute_SolverStandaloneResources_213

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame

/-- The complete EXACT solver conjunct of the original uniform rational
implementation target. Program and positive constants precede EVERY P,
fee, arbitrary rational penalty and arbitrary original n/k. -/
theorem solver_uniform_original :
    ∃ (solver : Program) (Ctime Cspace Cbits : ℕ),
      0<Ctime ∧ 0<Cspace ∧ 0<Cbits ∧
      ∀ (P : Parameters) (fee penalty : ℚ) (n k : ℕ),∃ trace final,
        Runs solver (solveInput P fee penalty n k) trace final ∧
        final.output=encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n) ∧
        time solver trace≤Ctime*(n+1)*(k+1)*(P.certificate.M+1) ∧
        peakCells trace≤Cspace*(n+1)*(k+1) ∧
        peakOperandBits trace≤Cbits*((n+1)*(2*(P.certificate.M+1)+2)*(maximumMenuBits P fee+1)+
          ratEncodingBits penalty+natBits n+natBits k+1) := by
  refine ⟨solverStandaloneProgram,40000,128,solverStandaloneBitConstant,by decide,by decide,?_,?_⟩
  · unfold solverStandaloneBitConstant
    omega
  · intro P fee penalty n k
    obtain ⟨trace,final,run,output,cost,space,bits,_⟩:=solver_standalone_resources P fee penalty n k
    refine ⟨trace,final,run,output,?_,?_,bits⟩
    · exact cost.trans_eq (by unfold entryCount;ring)
    · exact space.trans_eq (by unfold entryCount;ring)

end PDCompute.Solver
