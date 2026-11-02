module

public import Paid.PDCompute_SolverEndpointMemory_065

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem scanCandidateCode_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell) (P : Parameters)
    (before : State) (base source index n k : ℕ) (values : ℕ → Cell) (good bad : ℚ)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (hindex : index ≤ P.certificate.M)
    (hpointer : values 39=.natural (source+(1+2*index)))
    (hgood : values 21=.rational good) (hbad : values 22=.rational bad)
    (fetched : FetchesCode program before.pc (scanCandidateCode mode)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 1410 ∧ Header after base (scanCandidateValues P values index good bad) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+67 ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let endpoint := P.cachedEndpoint P.endpointCache index
  let endpointValues := scanEndpointValues values endpoint.error endpoint.charge
  have endpointFetch : FetchesCode program before.pc (scanEndpointCode mode) := by
    rw [scanCandidateCode] at fetched
    exact fetched.append_left
  obtain ⟨endpointTrace,endpointState,endpointHead,endpointLast,endpointChain,endpointTime,endpointHeader,
      endpointBase,endpointPC,endpointFrame,endpointOutput,endpointMemory⟩ :=
    scanEndpointCode_trace_memory mode program input P before base source index n k values
      header hbase hsource hindex hpointer endpointFetch
  have he : endpointValues 26=.rational endpoint.error := rfl
  have hc : endpointValues 27=.rational endpoint.charge := rfl
  have hg : endpointValues 21=.rational good := hgood
  have hb : endpointValues 22=.rational bad := hbad
  have scoreFetch : FetchesCode program endpointState.pc (headerCode candidateCommands) := by
    rw [endpointPC]
    rw [scanCandidateCode] at fetched
    exact fetched.append_right
  obtain ⟨scoreTrace,after,scoreHead,scoreLast,scoreChain,scoreTime,scoreHeader,scoreBase,scorePC,scoreFrame,scoreOutput,scoreMemory⟩ :=
    headerCode_trace_memory candidateCommands program input endpointState base n k endpointValues _
      candidateCommands_valid endpointHeader endpointBase
      (candidateCommands_eval endpointValues endpoint.error endpoint.charge good bad he hc hg hb) scoreFetch
  have joined := joinTrace_spec program input endpointTrace scoreTrace before endpointState after 255 1155
    endpointHead endpointLast scoreHead scoreLast endpointChain scoreChain endpointTime scoreTime
  refine ⟨joinTrace endpointTrace scoreTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    scoreHeader,scoreBase,?_,endpointFrame.trans scoreFrame,scoreOutput.trans endpointOutput,
    joinTrace_memory endpointTrace scoreTrace before endpointState base endpointLast endpointMemory scoreMemory⟩
  rw [scorePC,endpointPC,candidateCode_length]

end PDCompute.Solver
