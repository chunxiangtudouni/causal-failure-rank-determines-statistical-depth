module

public import Paid.PDCompute_SolverScanLoopMemory_069

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

/-- Original selected menu entry together with the live Header, all
non-scratch caller cells, and exact heap/live/output frame at EVERY actual
scan state. In particular older dense table cells are protected even
INSIDE the solver's larger workspace. -/
theorem scanKernel_caller_memory (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin))
    (P : Parameters) (base source n k : ℕ) (fee penalty : ℚ) (previous : MenuRow) (tools : ℕ)
    (nonzero : penalty ≠ 0) (avoids : EndpointAvoids mode P source base n k)
    (before : State) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hsource : EndpointSource mode input P source before)
    (last : values 6=.natural P.certificate.M)
    (good : values 21=.rational ((previous.getD tools abandonEntry).objective fee penalty))
    (bad : values 22=.rational ((P.menuBadBranch fee penalty previous tools).2.objective fee penalty))
    (bestLevel : values 23=.natural 0) (best : values 24=.rational penalty)
    (index : values 25=.natural 0) (pointer : values 39=.natural (source+1)) :
    let selected := cutoffScan
      (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)
      penalty P.certificate.M
    ∃ trace : List State, ∃ after : State, ∃ finalValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*(P.certificate.M+1)+135 ∧ Header after base finalValues ∧
      after.heap (base+23)=.natural selected.1 ∧ after.heap (base+24)=.rational selected.2 ∧
      after.register .fresh=.natural base ∧ after.pc=origin+112 ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace, HeaderMemory before state base) ∧ ScanPreserves values finalValues ∧
      P.cachedNextMenuEntry P.endpointCache fee penalty previous tools=
        if selected.2=penalty then abandonEntry else
          P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools selected.1 := by
  let goodValue := (previous.getD tools abandonEntry).objective fee penalty
  let badValue := (P.menuBadBranch fee penalty previous tools).2.objective fee penalty
  have contents : ScanContents P values source 0 goodValue badValue penalty :=
    ⟨last,good,bad,bestLevel,best,index,pointer⟩
  obtain ⟨trace,after,finalValues,hh,hl,hchain,ht,afterHeader,afterContents,afterBase,afterPC,afterFrame,afterOutput,memory,preserved⟩ :=
    scanKernel_iterations_memory mode program input origin hcode P base source n k goodValue badValue penalty avoids
      (P.certificate.M+1) before values 0 (by omega) hpc header hbase hsource contents
  have objective : (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)=
      affineEndpointScore P goodValue badValue := by
    funext level
    exact cachedTesting_objective_affine P fee penalty previous tools level
  refine ⟨trace,after,finalValues,hh,hl,hchain,ht,afterHeader,?_,?_,afterBase,afterPC,afterFrame,afterOutput,
    memory,preserved,?_⟩
  · have heap := (afterHeader.value 23 (by decide)).trans afterContents.bestLevel
    rw [cutoffPrefix_succ] at heap
    simpa only [objective] using heap
  · have heap := (afterHeader.value 24 (by decide)).trans afterContents.bestValue
    rw [cutoffPrefix_succ] at heap
    simpa only [objective] using heap
  · exact cachedNextMenuEntry_cutoff P fee penalty previous tools nonzero

end PDCompute.Solver
