module

public import Paid.PDCompute_SolverScanTestBits_178
public import Paid.PDCompute_SolverScanBodyBits_180
public import Paid.PDCompute_SolverScanLoopMemory_069

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Actual complete M+1 endpoint scan. Every original iteration reads,
computes, chooses, increments and returns; ALL prefixes use ONE budget.
The penalty/cutoff is only compared or copied across iterations. -/
theorem scanKernel_iterations_bits (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (fetch : FetchesCode program origin (scanKernel mode origin))
    (P : Parameters) (fee : ℚ) (base source n k budget G : ℕ) (good bad cutoff : ℚ)
    (avoids : EndpointAvoids mode P source base n k) (remaining : ℕ)
    (before : State) (values : ℕ → Cell) (index : ℕ) (finish : index+remaining=P.certificate.M+1)
    (hpc : before.pc=origin) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (contents : ScanContents P values source index good bad cutoff)
    (safe : RootD27.Bits.SafeBits before budget) (goodBits : ratEncodingBits good≤G) (badBits : ratEncodingBits bad≤G)
    (room : 1+64*(maximumMenuBits P fee+G+1)≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget) (pcBits : natBits (origin+112)≤budget) :
    ∃ trace : List State,∃ after : State,∃ finalValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤2500*remaining+135 ∧ Header after base finalValues ∧
      ScanContents P finalValues source (P.certificate.M+1) good bad cutoff ∧ after.register .fresh=.natural base ∧ after.pc=origin+112 ∧
      Frame before after base n k ∧ after.output=before.output ∧ (∀ state∈trace,HeaderMemory before state base) ∧
      ScanPreserves values finalValues ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  have small : 4≤budget := by omega
  induction remaining generalizing before values index with
  | zero =>
    have indexEq : index=P.certificate.M+1 := by omega
    subst index
    obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterBase,afterPC,afterFrame,afterOutput,memory,bounded⟩:=
      scanKernel_test_trace_bits mode program input origin fetch before base n k (P.certificate.M+1) P.certificate.M budget values
        hpc header fresh contents.counter contents.last safe small addressBits pcBits
    have beyond : ¬P.certificate.M+1≤P.certificate.M := by omega
    exact ⟨trace,after,values,head,last,chain,cost,afterHeader,contents,afterBase,
      by simpa only [ite_eq_right beyond] using afterPC,afterFrame,afterOutput,memory,ScanPreserves.refl values,bounded⟩
  | succ remaining ih =>
    have inside : index≤P.certificate.M := by omega
    obtain ⟨testTrace,tested,testHead,testLast,testChain,testTime,testHeader,testBase,testPC,testFrame,testOutput,testMemory,testSafe⟩:=
      scanKernel_test_trace_bits mode program input origin fetch before base n k index P.certificate.M budget values
        hpc header fresh contents.counter contents.last safe small addressBits pcBits
    have bodyPC : tested.pc=origin+8 := by simpa only [ite_eq_left inside] using testPC
    have testSource:=EndpointSource.frame_of_avoids mode input P source base n k before tested hsource avoids testFrame
    let nextValues:=scanIterationValues P values index source good bad (cutoffPrefix (affineEndpointScore P good bad) cutoff index).2
    obtain ⟨bodyTrace,advanced,bodyHead,bodyLast,bodyChain,bodyTime,bodyHeader,bodyBase,bodyReturned,bodyFrame,bodyOutput,bodyMemory,bodySafe⟩:=
      scanKernel_body_trace_bits mode program input origin fetch tested P fee base source index n k budget G values good bad
        (cutoffPrefix (affineEndpointScore P good bad) cutoff index).2 bodyPC testHeader testBase testSource inside
        contents.pointer contents.counter contents.goodValue contents.badValue contents.bestValue
        (testSafe tested (List.mem_of_getLast? testLast)) goodBits badBits room addressBits indexBits sourceBits pcBits
    have nextSource:=EndpointSource.frame_of_avoids mode input P source base n k tested advanced testSource avoids bodyFrame
    have nextFinish : index+1+remaining=P.certificate.M+1 := by omega
    obtain ⟨tail,after,finalValues,tailHead,tailLast,tailChain,tailTime,afterHeader,afterContents,afterBase,afterPC,afterFrame,afterOutput,tailMemory,preserved,tailSafe⟩:=
      ih advanced nextValues (index+1) nextFinish bodyReturned bodyHeader bodyBase nextSource contents.next
        (bodySafe advanced (List.mem_of_getLast? bodyLast))
    have frontJoin:=joinTrace_spec program input testTrace bodyTrace before tested advanced 135 2325
      testHead testLast bodyHead bodyLast testChain bodyChain testTime bodyTime
    have frontMemory:=joinTrace_memory testTrace bodyTrace before tested base testLast testMemory bodyMemory
    have frontSafe:=PDCompute.Pack.joinTrace_invariant testTrace bodyTrace (fun state=>RootD27.Bits.SafeBits state budget) testSafe bodySafe
    have allJoin:=joinTrace_spec program input (joinTrace testTrace bodyTrace) tail before advanced after 2460 (2500*remaining+135)
      frontJoin.1 frontJoin.2.1 tailHead tailLast frontJoin.2.2.1 tailChain frontJoin.2.2.2 tailTime
    refine ⟨joinTrace (joinTrace testTrace bodyTrace) tail,after,finalValues,allJoin.1,allJoin.2.1,allJoin.2.2.1,?_,afterHeader,afterContents,afterBase,afterPC,
      testFrame.trans (bodyFrame.trans afterFrame),afterOutput.trans (bodyOutput.trans testOutput),
      joinTrace_memory (joinTrace testTrace bodyTrace) tail before advanced base frontJoin.2.1 frontMemory tailMemory,
      (scanIterationValues_preserves_header P values index source good bad _).trans preserved,
      PDCompute.Pack.joinTrace_invariant (joinTrace testTrace bodyTrace) tail (fun state=>RootD27.Bits.SafeBits state budget) frontSafe tailSafe⟩
    omega

end PDCompute.Solver
