module

public import Paid.RootD27Endpoint_CacheHeap_018
public import Paid.RootD27Endpoint_Control_011
public import Paid.RootD27Endpoint_Return_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem trace_last_member (trace : List State) (state : State) (last : trace.getLast?=some state) : state∈trace := by
  have split:=List.dropLast_append_getLast? state (by rw [last]; simp)
  rw [←split]
  simp

theorem loop_budget_succ (fuel : ℕ) : 2370+(2370*fuel+360)=2370*(fuel+1)+360 := by
  rw [Nat.mul_succ]
  ac_rfl

/-- Induction counts the remaining real iterations. The equation is
discharged with m=0/fuel=M+1 by the complete entry producer; no caller
fuel oracle, supplied cache, synthetic return or attained optimum. -/
theorem loop_cache_actual (P : Parameters) (program : Program) (input : List Cell)
    (base E returnPC testPC bodyPC exitPC : ℕ) (separated : base+48≤E)
    (testFetch : FetchesCode program testPC (rowTestCode bodyPC exitPC))
    (bodyFetch : FetchesCode program bodyPC (rowBodyCode testPC))
    (returnFetch : FetchesCode program exitPC returnCode)
    (fuel m : ℕ) (before : State) (values : ℕ → Cell)
    (position : before.pc=testPC) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (invariant : EndpointValues P E returnPC m values)
    (stored : StoredCache P E m before) (remaining : m+fuel=P.certificate.M+1) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2370*fuel+360 ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural E ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      StoredCache P E (P.certificate.M+1) after ∧ after.output=before.output := by
  induction fuel generalizing m before values with
  | zero =>
    have finished : m=P.certificate.M+1 := by omega
    have outside : ¬m≤P.certificate.M := by omega
    obtain ⟨testTrace,tested,th,tl,tc,tt,testedPC,testedFresh,testedHeader,testMemory⟩:=
      rowTest_actual program input before base m P.certificate.M bodyPC exitPC values header fresh
        invariant.counter invariant.stop (by rw [position]; exact testFetch)
    have exit : tested.pc=exitPC := by simpa only [ite_eq_right outside] using testedPC
    have unchanged:=testMemory tested (trace_last_member testTrace tested tl)
    obtain ⟨returnTrace,after,rh,rl,rc,rt,afterPC,afterFresh,afterOld,afterAddress,afterIndex,returnMemory⟩:=
      return_actual program input tested base E P.certificate.M returnPC values testedHeader testedFresh
        invariant.cache invariant.stop invariant.ret (by rw [exit]; exact returnFetch)
    have finalMemory:=returnMemory after (trace_last_member returnTrace after rl)
    have storedTest : StoredCache P E (P.certificate.M+1) tested := by
      rw [←finished]
      exact stored.congr unchanged.1 unchanged.2.1
    have joined:=joinTrace_spec program input testTrace returnTrace before tested after
      135 225 th tl rh rl tc rc tt rt
    exact ⟨joinTrace testTrace returnTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
      afterPC,afterFresh,afterOld,afterAddress,afterIndex,
      storedTest.congr finalMemory.1 finalMemory.2.1,finalMemory.2.2.trans unchanged.2.2⟩
  | succ fuel ih =>
    have inside : m≤P.certificate.M := by omega
    obtain ⟨testTrace,tested,th,tl,tc,tt,testedPC,testedFresh,testedHeader,testMemory⟩:=
      rowTest_actual program input before base m P.certificate.M bodyPC exitPC values header fresh
        invariant.counter invariant.stop (by rw [position]; exact testFetch)
    have bodyPosition : tested.pc=bodyPC := by simpa only [ite_eq_left inside] using testedPC
    have unchanged:=testMemory tested (trace_last_member testTrace tested tl)
    obtain ⟨bodyTrace,bodyAfter,bh,bl,bc,bt,bodyPC',bodyFresh,bodyHeader,bodyInvariant,bodyStored,bodyOutput⟩:=
      EndpointValues.actual_body_cache P m program input tested base E returnPC testPC values
        testedHeader testedFresh invariant (stored.congr unchanged.1 unchanged.2.1) separated
        (by rw [bodyPosition]; exact bodyFetch)
    obtain ⟨later,after,lh,ll,lc,lt,afterPC,afterFresh,afterOld,afterAddress,afterIndex,afterStored,afterOutput⟩:=
      ih (m:=m+1) (before:=bodyAfter) (values:=bodyValues P values m) bodyPC' bodyHeader bodyFresh
        bodyInvariant bodyStored (by omega)
    have first:=joinTrace_spec program input testTrace bodyTrace before tested bodyAfter
      135 2235 th tl bh bl tc bc tt bt
    have joined:=joinTrace_spec program input (joinTrace testTrace bodyTrace) later before bodyAfter after
      2370 (2370*fuel+360) first.1 first.2.1 lh ll first.2.2.1 lc first.2.2.2 lt
    refine ⟨joinTrace (joinTrace testTrace bodyTrace) later,after,joined.1,joined.2.1,joined.2.2.1,?_,
      afterPC,afterFresh,afterOld,afterAddress,afterIndex,afterStored,
      afterOutput.trans (bodyOutput.trans unchanged.2.2)⟩
    calc
      _≤2370+(2370*fuel+360) := joined.2.2.2
      _=2370*(fuel+1)+360 := loop_budget_succ fuel

theorem full_loop_original_cache (P : Parameters) (program : Program) (input : List Cell)
    (base E returnPC testPC bodyPC exitPC : ℕ) (separated : base+48≤E)
    (testFetch : FetchesCode program testPC (rowTestCode bodyPC exitPC))
    (bodyFetch : FetchesCode program bodyPC (rowBodyCode testPC))
    (returnFetch : FetchesCode program exitPC returnCode)
    (before : State) (values : ℕ → Cell) (position : before.pc=testPC)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (invariant : EndpointValues P E returnPC 0 values) (stored : StoredCache P E 0 before) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2370*(P.certificate.M+1)+360 ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural E ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      HeapList after E (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output := by
  obtain ⟨trace,after,hh,hl,hc,ht,hpc,hf,ho,ha,hi,storedAfter,output⟩:=
    loop_cache_actual P program input base E returnPC testPC bodyPC exitPC separated testFetch bodyFetch returnFetch
      (P.certificate.M+1) 0 before values position header fresh invariant stored (by omega)
  exact ⟨trace,after,hh,hl,hc,ht,hpc,hf,ho,ha,hi,storedAfter.original_codec,output⟩

end RootD27.Endpoint
