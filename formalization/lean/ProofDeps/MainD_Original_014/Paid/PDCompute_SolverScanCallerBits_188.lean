module

public import Paid.PDCompute_SolverScanLoopBits_181
public import Paid.PDCompute_SolverScanCallerMemory_070

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Original selected level/score on the SAME actual full M+1 scan
that has all-prefix memory and complete-state operand bounds. -/
theorem scanKernel_caller_bits (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (fetch : FetchesCode program origin (scanKernel mode origin)) (P : Parameters)
    (base source n k budget G : ℕ) (fee penalty : ℚ) (previous : MenuRow) (tools : ℕ)
    (nonzero : penalty≠0) (avoids : EndpointAvoids mode P source base n k) (before : State) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (last : values 6=.natural P.certificate.M)
    (good : values 21=.rational ((previous.getD tools abandonEntry).objective fee penalty))
    (bad : values 22=.rational ((P.menuBadBranch fee penalty previous tools).2.objective fee penalty))
    (bestLevel : values 23=.natural 0) (best : values 24=.rational penalty) (index : values 25=.natural 0) (pointer : values 39=.natural (source+1))
    (safe : RootD27.Bits.SafeBits before budget)
    (goodBits : ratEncodingBits ((previous.getD tools abandonEntry).objective fee penalty)≤G)
    (badBits : ratEncodingBits ((P.menuBadBranch fee penalty previous tools).2.objective fee penalty)≤G)
    (room : 1+64*(maximumMenuBits P fee+G+1)≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (indexBits : 1+natBits (P.certificate.M+1)≤budget) (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget)
    (pcBits : natBits (origin+112)≤budget) :
    let selected:=cutoffScan (fun level=>(P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty) penalty P.certificate.M
    ∃ trace : List State,∃ after : State,∃ finalValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤2500*(P.certificate.M+1)+135 ∧ Header after base finalValues ∧
      after.heap (base+23)=.natural selected.1 ∧ after.heap (base+24)=.rational selected.2 ∧ after.register .fresh=.natural base ∧ after.pc=origin+112 ∧
      Frame before after base n k ∧ after.output=before.output ∧ (∀ state∈trace,HeaderMemory before state base) ∧ ScanPreserves values finalValues ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧ P.cachedNextMenuEntry P.endpointCache fee penalty previous tools=
        if selected.2=penalty then abandonEntry else P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools selected.1 := by
  let goodValue:=(previous.getD tools abandonEntry).objective fee penalty
  let badValue:=(P.menuBadBranch fee penalty previous tools).2.objective fee penalty
  have contents : ScanContents P values source 0 goodValue badValue penalty := ⟨last,good,bad,bestLevel,best,index,pointer⟩
  obtain ⟨trace,after,finalValues,head,lastState,chain,cost,afterHeader,afterContents,afterBase,afterPC,frame,output,memory,preserved,bounded⟩:=
    scanKernel_iterations_bits mode program input origin fetch P fee base source n k budget G goodValue badValue penalty avoids
      (P.certificate.M+1) before values 0 (by omega) hpc header fresh hsource contents safe goodBits badBits room addressBits indexBits sourceBits pcBits
  have objective : (fun level=>(P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)=affineEndpointScore P goodValue badValue := by
    funext level
    exact cachedTesting_objective_affine P fee penalty previous tools level
  refine ⟨trace,after,finalValues,head,lastState,chain,cost,afterHeader,?_,?_,afterBase,afterPC,frame,output,memory,preserved,bounded,?_⟩
  · have heap:=(afterHeader.value 23 (by decide)).trans afterContents.bestLevel
    rw [cutoffPrefix_succ] at heap
    simpa only [objective] using heap
  · have heap:=(afterHeader.value 24 (by decide)).trans afterContents.bestValue
    rw [cutoffPrefix_succ] at heap
    simpa only [objective] using heap
  · exact cachedNextMenuEntry_cutoff P fee penalty previous tools nonzero

end PDCompute.Solver
