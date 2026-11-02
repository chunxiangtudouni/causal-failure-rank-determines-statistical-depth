module

public import Paid.PDCompute_SolverScanEndpointBits_174
public import Paid.PDCompute_SolverCandidateBits_156
public import Paid.PDCompute_SolverScanCandidate_039

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Original67-op cache read and affine score on ONE actual fetched trace.
The original endpoint bits pay the cache scalars; the fixed-depth
objective arithmetic never accumulates a bound over scan iterations. -/
theorem scanCandidateCode_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell) (P : Parameters) (fee : ℚ)
    (before : State) (base source index n k budget G : ℕ) (values : ℕ → Cell) (good bad : ℚ)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (hindex : index≤P.certificate.M)
    (hpointer : values 39=.natural (source+(1+2*index))) (hgood : values 21=.rational good) (hbad : values 22=.rational bad)
    (safe : RootD27.Bits.SafeBits before budget) (goodBits : ratEncodingBits good≤G) (badBits : ratEncodingBits bad≤G)
    (room : 1+64*(maximumMenuBits P fee+G+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget)
    (pointerBits : 1+natBits ((source+(1+2*index))+1)≤budget) (counter : natBits (before.pc+67)≤budget)
    (fetch : FetchesCode program before.pc (scanCandidateCode mode)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤1410 ∧
      Header after base (scanCandidateValues P values index good bad) ∧ after.register .fresh=.natural base ∧ after.pc=before.pc+67 ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let endpoint:=P.cachedEndpoint P.endpointCache index
  let readValues:=scanEndpointValues values endpoint.error endpoint.charge
  have small : 4≤budget := by omega
  have cacheBits : 1+maximumMenuBits P fee≤budget := by omega
  obtain ⟨readTrace,readState,readHead,readLast,readChain,readTime,readHeader,readBase,readPC,readFrame,readOutput,readMemory,readSafe⟩:=
    scanEndpointCode_trace_bits mode program input P fee before base source index n k budget values header fresh hsource hindex hpointer
      safe small cacheBits addressBits pointerBits ((natBits_mono (by omega : before.pc+13≤before.pc+67)).trans counter) fetch.append_left
  have errorValue : readValues 26=.rational endpoint.error := by simp only [readValues,scanEndpointValues,Function.update_apply]; rfl
  have chargeValue : readValues 27=.rational endpoint.charge := by simp only [readValues,scanEndpointValues,Function.update_self]
  have goodValue : readValues 21=.rational good := hgood
  have badValue : readValues 22=.rational bad := hbad
  have endpointBits:=originalEndpoint_cellBits P fee index hindex
  have errorBound : ratEncodingBits endpoint.error≤maximumMenuBits P fee := by
    have actual : 1+ratEncodingBits endpoint.error≤1+maximumMenuBits P fee := endpointBits.1
    omega
  have chargeBound : ratEncodingBits endpoint.charge≤maximumMenuBits P fee := by
    have actual : 1+ratEncodingBits endpoint.charge≤1+maximumMenuBits P fee := endpointBits.2
    omega
  have scoreCounter : natBits (readState.pc+54)≤budget := by rw [readPC]; simpa only [Nat.add_assoc] using counter
  have scoreFetch : FetchesCode program readState.pc (headerCode candidateCommands) := by rw [readPC]; exact fetch.append_right
  obtain ⟨scoreTrace,after,scoreHead,scoreLast,scoreChain,scoreTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,scoreResources⟩:=
    candidateCode_trace_bits program input readState base n k budget (maximumMenuBits P fee) G readValues endpoint.error endpoint.charge good bad
      readHeader readBase (readSafe readState (List.mem_of_getLast? readLast)) errorValue chargeValue goodValue badValue
      errorBound chargeBound goodBits badBits room addressBits scoreCounter scoreFetch
  have scoreMemory : ∀ state∈scoreTrace,HeaderMemory readState state base := fun state member=>(scoreResources state member).1
  have scoreSafe : ∀ state∈scoreTrace,RootD27.Bits.SafeBits state budget := fun state member=>(scoreResources state member).2
  have joined:=joinTrace_spec program input readTrace scoreTrace before readState after 255 1155 readHead readLast scoreHead scoreLast
    readChain scoreChain readTime scoreTime
  refine ⟨joinTrace readTrace scoreTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,afterBase,?_,
    readFrame.trans afterFrame,afterOutput.trans readOutput,joinTrace_memory readTrace scoreTrace before readState base readLast readMemory scoreMemory,
    PDCompute.Pack.joinTrace_invariant readTrace scoreTrace (fun state=>RootD27.Bits.SafeBits state budget) readSafe scoreSafe⟩
  rw [afterPC,readPC]

end PDCompute.Solver
