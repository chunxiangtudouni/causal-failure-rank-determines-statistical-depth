module

public import Paid.PDCompute_SolverAdvanceMemory_067
public import Paid.PDCompute_SolverScanInvariant_048

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem scanKernel_body_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) (before : State)
    (P : Parameters) (base source index n k : ℕ) (values : ℕ → Cell) (good bad best : ℚ)
    (hpc : before.pc=origin+8) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (hindex : index ≤ P.certificate.M)
    (hpointer : values 39=.natural (source+(1+2*index))) (hcounter : values 25=.natural index)
    (hgood : values 21=.rational good) (hbad : values 22=.rational bad) (hbest : values 24=.rational best) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2325 ∧ Header after base (scanIterationValues P values index source good bad best) ∧
      after.register .fresh=.natural base ∧ after.pc=origin ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let candidateValues := scanCandidateValues P values index good bad
  let endpoint := P.cachedEndpoint P.endpointCache index
  let score := endpoint.charge+(1-endpoint.error)*good+endpoint.error*bad
  let minimumValues := if score < best then minimumUpdateValues candidateValues else candidateValues
  obtain ⟨scoreTrace,scored,scoreHead,scoreLast,scoreChain,scoreTime,scoreHeader,scoreBase,scorePC,scoreFrame,scoreOutput,scoreMemory⟩ :=
    scanCandidateCode_trace_memory mode program input P before base source index n k values good bad
      header hbase hsource hindex hpointer hgood hbad (scanKernel_candidate_fetch mode program origin hcode before hpc)
  have atMinimum : scored.pc=origin+75 := by rw [scorePC,hpc]
  have candidateScore : candidateValues 28=.rational score := scanCandidateValues_objective P values index good bad
  have candidateBest : candidateValues 24=.rational best :=
    (scanCandidateValues_preserves P values index good bad 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbest
  obtain ⟨minimumTrace,minimum,minimumHead,minimumLast,minimumChain,minimumTime,minimumHeader,minimumBase,
      minimumPC,minimumFrame,minimumOutput,minimumMemory⟩ :=
    minimumUpdateCode_trace_memory program input (origin+75) (scanKernel_minimum_fetch mode program origin hcode)
      scored base n k candidateValues score best atMinimum scoreHeader scoreBase candidateScore candidateBest
  have atAdvance : minimum.pc=origin+95 := by rw [minimumPC]
  have candidateCounter : candidateValues 25=.natural index :=
    (scanCandidateValues_preserves P values index good bad 25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcounter
  have candidatePointer : candidateValues 39=.natural (source+(1+2*index)) :=
    (scanCandidateValues_preserves P values index good bad 39 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpointer
  have minimumCounter : minimumValues 25=.natural index := by
    dsimp only [minimumValues]
    split
    · exact (minimumUpdateValues_preserves candidateValues 25 (by decide) (by decide)).trans candidateCounter
    · exact candidateCounter
  have minimumPointer : minimumValues 39=.natural (source+(1+2*index)) := by
    dsimp only [minimumValues]
    split
    · exact (minimumUpdateValues_preserves candidateValues 39 (by decide) (by decide)).trans candidatePointer
    · exact candidatePointer
  obtain ⟨advanceTrace,after,advanceHead,advanceLast,advanceChain,advanceTime,afterHeader,afterBase,afterPC,
      afterFrame,afterOutput,advanceMemory⟩ :=
    scanKernel_advance_trace_memory mode program input origin hcode minimum base n k index (source+(1+2*index))
      minimumValues atAdvance minimumHeader minimumBase minimumCounter minimumPointer
  have firstJoin := joinTrace_spec program input scoreTrace minimumTrace before scored minimum 1410 630
    scoreHead scoreLast minimumHead minimumLast scoreChain minimumChain scoreTime minimumTime
  have firstMemory := joinTrace_memory scoreTrace minimumTrace before scored base scoreLast scoreMemory minimumMemory
  have secondJoin := joinTrace_spec program input (joinTrace scoreTrace minimumTrace) advanceTrace before minimum after 2040 285
    firstJoin.1 firstJoin.2.1 advanceHead advanceLast firstJoin.2.2.1 advanceChain firstJoin.2.2.2 advanceTime
  exact ⟨joinTrace (joinTrace scoreTrace minimumTrace) advanceTrace,after,secondJoin.1,secondJoin.2.1,
    secondJoin.2.2.1,secondJoin.2.2.2,afterHeader,afterBase,afterPC,
    scoreFrame.trans (minimumFrame.trans afterFrame),afterOutput.trans (minimumOutput.trans scoreOutput),
    joinTrace_memory (joinTrace scoreTrace minimumTrace) advanceTrace before minimum base firstJoin.2.1 firstMemory advanceMemory⟩

end PDCompute.Solver
