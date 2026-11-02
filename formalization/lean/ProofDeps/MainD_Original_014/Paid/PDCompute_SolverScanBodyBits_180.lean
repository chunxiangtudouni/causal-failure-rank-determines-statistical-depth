module

public import Paid.PDCompute_SolverScanCandidateBits_175
public import Paid.PDCompute_SolverMinimumBits_168
public import Paid.PDCompute_SolverScanAdvanceBits_179
public import Paid.PDCompute_SolverScanInvariant_048

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- One genuine scan body: original endpoint read, original affine
arithmetic, strict minimum choice, two real increments and back-edge.
ALL resources belong to this same composed actual execution. -/
theorem scanKernel_body_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (fetch : FetchesCode program origin (scanKernel mode origin)) (before : State)
    (P : Parameters) (fee : ℚ) (base source index n k budget G : ℕ) (values : ℕ → Cell) (good bad best : ℚ)
    (hpc : before.pc=origin+8) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (hindex : index≤P.certificate.M)
    (hpointer : values 39=.natural (source+(1+2*index))) (hcounter : values 25=.natural index)
    (hgood : values 21=.rational good) (hbad : values 22=.rational bad) (hbest : values 24=.rational best)
    (safe : RootD27.Bits.SafeBits before budget) (goodBits : ratEncodingBits good≤G) (badBits : ratEncodingBits bad≤G)
    (room : 1+64*(maximumMenuBits P fee+G+1)≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget) (pcBits : natBits (origin+112)≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤2325 ∧
      Header after base (scanIterationValues P values index source good bad best) ∧ after.register .fresh=.natural base ∧ after.pc=origin ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let scoredValues:=scanCandidateValues P values index good bad
  let endpoint:=P.cachedEndpoint P.endpointCache index
  let score:=endpoint.charge+(1-endpoint.error)*good+endpoint.error*bad
  let minimumValues:=if score<best then minimumUpdateValues scoredValues else scoredValues
  have small : 4≤budget := by omega
  have readPointerBits : 1+natBits ((source+(1+2*index))+1)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : source+(1+2*index)+1≤source+(1+2*(P.certificate.M+1)))) 1).trans sourceBits
  have scoreCounter : natBits (before.pc+67)≤budget :=
    (natBits_mono (by rw [hpc]; omega : before.pc+67≤origin+112)).trans pcBits
  obtain ⟨scoreTrace,scored,scoreHead,scoreLast,scoreChain,scoreTime,scoreHeader,scoreBase,scorePC,scoreFrame,scoreOutput,scoreMemory,scoreSafe⟩:=
    scanCandidateCode_trace_bits mode program input P fee before base source index n k budget G values good bad header fresh hsource hindex hpointer hgood hbad
      safe goodBits badBits room addressBits readPointerBits scoreCounter (scanKernel_candidate_fetch mode program origin fetch before hpc)
  have atMinimum : scored.pc=origin+75 := by rw [scorePC,hpc]
  have candidateScore : scoredValues 28=.rational score := scanCandidateValues_objective P values index good bad
  have candidateBest : scoredValues 24=.rational best :=
    (scanCandidateValues_preserves P values index good bad 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbest
  obtain ⟨minimumTrace,minimum,minimumHead,minimumLast,minimumChain,minimumTime,minimumHeader,minimumBase,minimumPC,minimumFrame,minimumOutput,minimumMemory,minimumSafe⟩:=
    minimumUpdate_trace_bits program input (origin+75) scored base n k budget scoredValues score best atMinimum scoreHeader scoreBase candidateScore candidateBest
      (scoreSafe scored (List.mem_of_getLast? scoreLast)) small addressBits
      ((natBits_mono (by omega : origin+75+20≤origin+112)).trans pcBits) (scanKernel_minimum_fetch mode program origin fetch)
  have atAdvance : minimum.pc=origin+95 := by rw [minimumPC]
  have candidateCounter : scoredValues 25=.natural index :=
    (scanCandidateValues_preserves P values index good bad 25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcounter
  have candidatePointer : scoredValues 39=.natural (source+(1+2*index)) :=
    (scanCandidateValues_preserves P values index good bad 39 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpointer
  have minimumCounter : minimumValues 25=.natural index := by
    dsimp only [minimumValues]
    split
    · exact (minimumUpdateValues_preserves scoredValues 25 (by decide) (by decide)).trans candidateCounter
    · exact candidateCounter
  have minimumPointer : minimumValues 39=.natural (source+(1+2*index)) := by
    dsimp only [minimumValues]
    split
    · exact (minimumUpdateValues_preserves scoredValues 39 (by decide) (by decide)).trans candidatePointer
    · exact candidatePointer
  obtain ⟨advanceTrace,after,advanceHead,advanceLast,advanceChain,advanceTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,advanceMemory,advanceSafe⟩:=
    scanKernel_advance_trace_bits mode program input origin fetch minimum base n k index (source+(1+2*index)) budget minimumValues
      atAdvance minimumHeader minimumBase minimumCounter minimumPointer (minimumSafe minimum (List.mem_of_getLast? minimumLast)) small addressBits
      ((Nat.add_le_add_left (natBits_mono (by omega : index+1≤P.certificate.M+1)) 1).trans indexBits)
      ((Nat.add_le_add_left (natBits_mono (by omega : source+(1+2*index)+2≤source+(1+2*(P.certificate.M+1)))) 1).trans sourceBits) pcBits
  have firstJoin:=joinTrace_spec program input scoreTrace minimumTrace before scored minimum 1410 630 scoreHead scoreLast minimumHead minimumLast scoreChain minimumChain scoreTime minimumTime
  have firstMemory:=joinTrace_memory scoreTrace minimumTrace before scored base scoreLast scoreMemory minimumMemory
  have firstSafe:=PDCompute.Pack.joinTrace_invariant scoreTrace minimumTrace (fun state=>RootD27.Bits.SafeBits state budget) scoreSafe minimumSafe
  have secondJoin:=joinTrace_spec program input (joinTrace scoreTrace minimumTrace) advanceTrace before minimum after 2040 285
    firstJoin.1 firstJoin.2.1 advanceHead advanceLast firstJoin.2.2.1 advanceChain firstJoin.2.2.2 advanceTime
  exact ⟨joinTrace (joinTrace scoreTrace minimumTrace) advanceTrace,after,secondJoin.1,secondJoin.2.1,secondJoin.2.2.1,secondJoin.2.2.2,afterHeader,afterBase,afterPC,
    scoreFrame.trans (minimumFrame.trans afterFrame),afterOutput.trans (minimumOutput.trans scoreOutput),
    joinTrace_memory (joinTrace scoreTrace minimumTrace) advanceTrace before minimum base firstJoin.2.1 firstMemory advanceMemory,
    PDCompute.Pack.joinTrace_invariant (joinTrace scoreTrace minimumTrace) advanceTrace (fun state=>RootD27.Bits.SafeBits state budget) firstSafe advanceSafe⟩

end PDCompute.Solver
