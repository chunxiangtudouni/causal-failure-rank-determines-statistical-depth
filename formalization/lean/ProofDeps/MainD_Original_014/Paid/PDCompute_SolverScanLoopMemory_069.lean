module

public import Paid.PDCompute_SolverScanBodyMemory_068

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def ScanUntouched (slot : ℕ) : Prop :=
  slot ≠ 23 ∧ slot ≠ 24 ∧ slot ≠ 25 ∧ slot ≠ 26 ∧ slot ≠ 27 ∧
    slot ≠ 28 ∧ slot ≠ 29 ∧ slot ≠ 30 ∧ slot ≠ 39

def ScanPreserves (before after : ℕ → Cell) : Prop :=
  ∀ slot, ScanUntouched slot → after slot=before slot

theorem ScanPreserves.refl (values : ℕ → Cell) : ScanPreserves values values := fun _ _ => rfl

theorem ScanPreserves.trans {before middle after : ℕ → Cell}
    (first : ScanPreserves before middle) (later : ScanPreserves middle after) : ScanPreserves before after :=
  fun slot untouched => (later slot untouched).trans (first slot untouched)

theorem scanIterationValues_preserves_header (P : Parameters) (values : ℕ → Cell) (index source : ℕ) (good bad best : ℚ) :
    ScanPreserves values (scanIterationValues P values index source good bad best) := by
  intro slot untouched
  rcases untouched with ⟨h23,h24,h25,h26,h27,h28,h29,h30,h39⟩
  exact scanIterationValues_preserves P values index source slot good bad best h23 h24 h25 h26 h27 h28 h29 h30 h39

theorem scanKernel_iterations_memory (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin))
    (P : Parameters) (base source n k : ℕ) (good bad cutoff : ℚ)
    (avoids : EndpointAvoids mode P source base n k) (remaining : ℕ)
    (before : State) (values : ℕ → Cell) (index : ℕ)
    (finish : index+remaining=P.certificate.M+1)
    (hpc : before.pc=origin) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hsource : EndpointSource mode input P source before)
    (contents : ScanContents P values source index good bad cutoff) :
    ∃ trace : List State, ∃ after : State, ∃ finalValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 2500*remaining+135 ∧ Header after base finalValues ∧
      ScanContents P finalValues source (P.certificate.M+1) good bad cutoff ∧
      after.register .fresh=.natural base ∧ after.pc=origin+112 ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace, HeaderMemory before state base) ∧ ScanPreserves values finalValues := by
  induction remaining generalizing before values index with
  | zero =>
    have indexEq : index=P.certificate.M+1 := by omega
    subst index
    obtain ⟨trace,after,hh,hl,hchain,ht,afterHeader,afterBase,afterPC,afterFrame,afterOutput,memory⟩ :=
      scanKernel_test_trace_memory mode program input origin hcode before base n k (P.certificate.M+1) P.certificate.M values
        hpc header hbase contents.counter contents.last
    have beyond : ¬P.certificate.M+1 ≤ P.certificate.M := by omega
    exact ⟨trace,after,values,hh,hl,hchain,ht,afterHeader,contents,afterBase,
      by simpa only [ite_eq_right beyond] using afterPC,afterFrame,afterOutput,memory,ScanPreserves.refl values⟩
  | succ remaining ih =>
    have inside : index ≤ P.certificate.M := by omega
    obtain ⟨testTrace,tested,testHead,testLast,testChain,testTime,testHeader,testBase,testPC,testFrame,testOutput,testMemory⟩ :=
      scanKernel_test_trace_memory mode program input origin hcode before base n k index P.certificate.M values
        hpc header hbase contents.counter contents.last
    have bodyPC : tested.pc=origin+8 := by simpa only [ite_eq_left inside] using testPC
    have testSource := EndpointSource.frame_of_avoids mode input P source base n k before tested hsource avoids testFrame
    let nextValues := scanIterationValues P values index source good bad
      (cutoffPrefix (affineEndpointScore P good bad) cutoff index).2
    obtain ⟨bodyTrace,advanced,bodyHead,bodyLast,bodyChain,bodyTime,bodyHeader,bodyBase,bodyReturned,bodyFrame,bodyOutput,bodyMemory⟩ :=
      scanKernel_body_trace_memory mode program input origin hcode tested P base source index n k values good bad
        (cutoffPrefix (affineEndpointScore P good bad) cutoff index).2 bodyPC testHeader testBase testSource inside
          contents.pointer contents.counter contents.goodValue contents.badValue contents.bestValue
    have nextSource := EndpointSource.frame_of_avoids mode input P source base n k tested advanced testSource avoids bodyFrame
    have nextFinish : index+1+remaining=P.certificate.M+1 := by omega
    obtain ⟨tail,after,finalValues,tailHead,tailLast,tailChain,tailTime,afterHeader,afterContents,
        afterBase,afterPC,afterFrame,afterOutput,tailMemory,preserved⟩ :=
      ih advanced nextValues (index+1) nextFinish bodyReturned bodyHeader bodyBase nextSource contents.next
    have frontJoin := joinTrace_spec program input testTrace bodyTrace before tested advanced 135 2325
      testHead testLast bodyHead bodyLast testChain bodyChain testTime bodyTime
    have frontMemory := joinTrace_memory testTrace bodyTrace before tested base testLast testMemory bodyMemory
    have allJoin := joinTrace_spec program input (joinTrace testTrace bodyTrace) tail before advanced after 2460 (2500*remaining+135)
      frontJoin.1 frontJoin.2.1 tailHead tailLast frontJoin.2.2.1 tailChain frontJoin.2.2.2 tailTime
    refine ⟨joinTrace (joinTrace testTrace bodyTrace) tail,after,finalValues,allJoin.1,allJoin.2.1,
      allJoin.2.2.1,?_,afterHeader,afterContents,afterBase,afterPC,
      testFrame.trans (bodyFrame.trans afterFrame),afterOutput.trans (bodyOutput.trans testOutput),
      joinTrace_memory (joinTrace testTrace bodyTrace) tail before advanced base frontJoin.2.1 frontMemory tailMemory,
      (scanIterationValues_preserves_header P values index source good bad _).trans preserved⟩
    omega

end PDCompute.Solver
