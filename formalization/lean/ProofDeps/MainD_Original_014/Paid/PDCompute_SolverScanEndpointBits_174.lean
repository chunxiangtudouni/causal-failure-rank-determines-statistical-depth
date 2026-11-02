module

public import Paid.PDCompute_SolverEndpointHeaderBits_173
public import Paid.PDCompute_SolverFieldBits_151
public import Paid.PDCompute_SolverHeaderFrame_099

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (loadSlot loadSlotResult)

theorem originalEndpoint_cellBits (P : Parameters) (fee : ℚ) (index : ℕ) (inside : index≤P.certificate.M) :
    (.rational (P.cachedEndpoint P.endpointCache index).error : Cell).bits≤1+maximumMenuBits P fee ∧
    (.rational (P.cachedEndpoint P.endpointCache index).charge : Cell).bits≤1+maximumMenuBits P fee := by
  change 1+ratEncodingBits (P.cachedEndpoint P.endpointCache index).error≤1+maximumMenuBits P fee ∧
    1+ratEncodingBits (P.cachedEndpoint P.endpointCache index).charge≤1+maximumMenuBits P fee
  rw [cachedEndpoint_eq]
  have errors:=(maximumMenuBits_bound P fee).2 _ (endpoint_scalar_mem P fee index inside).1
  have charges:=(maximumMenuBits_bound P fee).2 _ (endpoint_scalar_mem P fee index inside).2
  exact ⟨Nat.add_le_add_left errors 1,Nat.add_le_add_left charges 1⟩

/-- Actual13-op scan endpoint read: real saved cursor, actual original
cache pair, real Header stores; SAME original source/word/PC invariants. -/
theorem scanEndpointCode_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell) (P : Parameters) (fee : ℚ)
    (before : State) (base source index n k budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (hindex : index≤P.certificate.M)
    (hpointer : values 39=.natural (source+(1+2*index))) (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (cacheBits : 1+maximumMenuBits P fee≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pointerBits : 1+natBits ((source+(1+2*index))+1)≤budget) (counter : natBits (before.pc+13)≤budget)
    (fetch : FetchesCode program before.pc (scanEndpointCode mode)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤255 ∧
      Header after base (scanEndpointValues values (P.cachedEndpoint P.endpointCache index).error (P.cachedEndpoint P.endpointCache index).charge) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+13 ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let endpoint:=P.cachedEndpoint P.endpointCache index
  let address:=source+(1+2*index)
  let pointed:=loadSlotResult before base 39 .address
  let after:=endpointHeaderResult pointed base address endpoint.error endpoint.charge
  have slotBits : 1+natBits (base+39)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by unfold headerWords; omega : base+39≤base+headerWords)) 1).trans addressBits
  obtain ⟨pointerTrace,pointerHead,pointerLast,pointerChain,pointerTime,pointerMemory,pointerSafe⟩:=PDCompute.Pack.loadSlot_trace_safe program input before base 39 budget .address values
    header (by decide) fresh safe slotBits ((natBits_mono (by omega : before.pc+3≤before.pc+13)).trans counter) fetch.append_left
  have pointedHeader : Header pointed base values := header
  have pointedBase : pointed.register .fresh=.natural base := (loadSlotResult_fresh before base 39 .address (by decide)).trans fresh
  have pointedAddress : pointed.register .address=.natural address := (header.loadSlot_execute input 39 .address (by decide) fresh).2.trans hpointer
  have pointedSource : EndpointSource mode input P source pointed := by cases mode <;> exact hsource
  have errorCell : mode.HasCell input pointed address (.rational endpoint.error) := EndpointSource.error mode input P source index pointed pointedSource hindex
  have chargeCell : mode.HasCell input pointed (address+1) (.rational endpoint.charge) := by
    simpa only [address,endpoint,Nat.add_assoc] using EndpointSource.charge mode input P source index pointed pointedSource hindex
  have valuesBits:=originalEndpoint_cellBits P fee index hindex
  have pointedCounter : natBits (pointed.pc+10)≤budget := by simpa only [pointed,loadSlotResult,Nat.add_assoc] using counter
  have pointedBound:=pointerSafe pointed (List.mem_of_getLast? pointerLast)
  obtain ⟨endpointTrace,endpointHead,endpointLast,endpointChain,endpointTime,endpointMemory,endpointSafe⟩:=
    endpointHeader_trace_bits mode program input pointed base address budget values endpoint.error endpoint.charge pointedHeader pointedBase pointedAddress errorCell chargeCell
      pointedBound small (valuesBits.1.trans cacheBits) (valuesBits.2.trans cacheBits) pointerBits addressBits pointedCounter fetch.append_right
  have joined:=joinTrace_spec program input pointerTrace endpointTrace before pointed after 60 195 pointerHead pointerLast endpointHead endpointLast
    pointerChain endpointChain pointerTime endpointTime
  have allMemory:=joinTrace_memory pointerTrace endpointTrace before pointed base pointerLast pointerMemory endpointMemory
  have finalMemory : HeaderMemory before after base := HeaderMemory.trace_last allMemory joined.2.1
  refine ⟨joinTrace pointerTrace endpointTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    endpointHeaderResult_header pointed base address endpoint.error endpoint.charge values pointedHeader,
    (endpointHeaderResult_fresh pointed base address endpoint.error endpoint.charge).trans pointedBase,?_,finalMemory.frame n k,finalMemory.2.2,allMemory,
    PDCompute.Pack.joinTrace_invariant pointerTrace endpointTrace (fun state=>RootD27.Bits.SafeBits state budget) pointerSafe endpointSafe⟩
  have finalPC:=endpointHeaderResult_pc pointed base address endpoint.error endpoint.charge
  simpa only [after,pointed,loadSlotResult,Nat.add_assoc] using finalPC

end PDCompute.Solver
