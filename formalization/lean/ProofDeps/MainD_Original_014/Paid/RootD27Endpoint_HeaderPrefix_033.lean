module

public import Paid.RootD27Endpoint_HeaderInit_006
public import Paid.PDCompute_SolverHeaderResources_140

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- Reuse the SAME real37-op producer. Its local finite operand budget
always exists for any caller state, so pure memory preservation adds no
new caller qualification or P-only scratch restriction. -/
theorem header_initialization_actual_region (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (base : ℕ) (position : before.pc=origin)
    (fresh : before.register .fresh=.natural base)
    (prologueFetch : FetchesCode program before.pc solverPrologue)
    (leadFetch : FetchesCode program (origin+16) paddingLeadCode)
    (loopFetch : FetchesCode program (origin+19) (baseRowCode (origin+19))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤2460 ∧
      Header after base (initializedHeaderValues (solverPrologueResult before base) base) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+37 ∧
      PDCompute.Solver.Frame before after base 0 0 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (cellRegion base headerWords) := by
  classical
  let oldBits:=(stateCellBits before).foldl max 0
  have oldSafe : RootD27.Bits.SafeBits before oldBits := by
    intro bits member
    have nonempty : stateCellBits before≠[] := by
      intro empty
      have lengths:=congrArg List.length empty
      simp only [stateCellBits,List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    change bits≤(stateCellBits before).foldl max 0
    rw [List.foldl_max_eq_max nonempty]
    exact (List.le_max_of_mem member).trans (le_max_right _ _)
  let budget:=oldBits+1+natBits (base+headerWords)+(.rational 0 : Cell).bits+natBits (origin+37)
  have safe : RootD27.Bits.SafeBits before budget :=
    fun bits member => (oldSafe bits member).trans (by dsimp only [budget];omega)
  have addressBits : 1+natBits (base+headerWords)≤budget := by dsimp only [budget];omega
  have zeroBits : (.rational 0 : Cell).bits≤budget := by dsimp only [budget];omega
  have pcBits : natBits (origin+37)≤budget := by dsimp only [budget];omega
  obtain ⟨trace,after,head,last,chain,cost,header,nextFresh,pc,frame,output,resources,_⟩:=
    solver_header_initialization_resources program input origin before base 0 0 budget position fresh
      safe addressBits zeroBits pcBits prologueFetch leadFetch loopFetch
  exact ⟨trace,after,head,last,chain,cost,header,nextFresh,pc,frame,output,
    fun state member => (resources state member).1⟩

end RootD27.Endpoint
