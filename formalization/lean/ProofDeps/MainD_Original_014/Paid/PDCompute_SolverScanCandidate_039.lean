module

public import Paid.PDCompute_SolverScanEndpoint_042

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute linearExecute_append loadSlot loadSlotResult storeSlotResult)
open PDMenu.ComputeFrame

def scanCandidateCode (mode : ReaderMode) : List Instruction :=
  scanEndpointCode mode++headerCode candidateCommands

def scanCandidateValues (P : Parameters) (values : ℕ → Cell) (index : ℕ) (good bad : ℚ) : ℕ → Cell :=
  let endpoint := P.cachedEndpoint P.endpointCache index
  candidateValues (Function.update (Function.update values 26 (.rational endpoint.error)) 27 (.rational endpoint.charge))
    endpoint.error endpoint.charge good bad

theorem scanCandidateCode_length (mode : ReaderMode) : (scanCandidateCode mode).length=67 := rfl

theorem scanCandidateCode_straight (mode : ReaderMode) : StraightCode (scanCandidateCode mode) := by
  intro instruction member
  simp only [scanCandidateCode,List.mem_append] at member
  rcases member with member|member
  · exact scanEndpointCode_straight mode instruction member
  · exact headerCode_straight candidateCommands instruction member

/-- The real streaming pointer is loaded from live slot39, the ORIGINAL
endpoint is read, then its affine score is really computed. All67 literal
instructions execute before the independent real strict-less branch. -/
theorem scanCandidateCode_execute (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (before : State) (base source index n k : ℕ) (values : ℕ → Cell) (good bad : ℚ)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (hindex : index ≤ P.certificate.M)
    (hpointer : values 39=.natural (source+(1+2*index)))
    (hgood : values 21=.rational good) (hbad : values 22=.rational bad) :
    ∃ after : State, linearExecute input (scanCandidateCode mode) before=some after ∧
      Header after base (scanCandidateValues P values index good bad) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+67 ∧
      Frame before after base n k ∧ after.output=before.output := by
  let endpoint := P.cachedEndpoint P.endpointCache index
  let endpointValues := scanEndpointValues values endpoint.error endpoint.charge
  obtain ⟨endpointState,endpointRun,endpointHeader,endpointBase,endpointPC,endpointFrame,endpointOutput⟩ :=
    scanEndpointCode_execute mode input P before base source index n k values header hbase hsource hindex hpointer
  have he : endpointValues 26=.rational endpoint.error := by simp only [endpointValues,scanEndpointValues,Function.update_apply]; rfl
  have hc : endpointValues 27=.rational endpoint.charge := by simp only [endpointValues,scanEndpointValues,Function.update_self]
  have hg : endpointValues 21=.rational good := hgood
  have hb : endpointValues 22=.rational bad := hbad
  obtain ⟨after,scoreRun,scoreHeader,scoreBase,scorePC,scoreFrame,scoreOutput⟩ :=
    headerCode_realize candidateCommands input endpointState base n k endpointValues _ candidateCommands_valid
      endpointHeader endpointBase (candidateCommands_eval endpointValues endpoint.error endpoint.charge good bad he hc hg hb)
  refine ⟨after,?_,scoreHeader,scoreBase,?_,endpointFrame.trans scoreFrame,scoreOutput.trans endpointOutput⟩
  · rw [scanCandidateCode,linearExecute_append,endpointRun,Option.bind_some]
    exact scoreRun
  · have scoreLength : (headerCode candidateCommands).length=54 := candidateCode_length
    rw [scorePC,endpointPC,scoreLength]

end PDCompute.Solver
