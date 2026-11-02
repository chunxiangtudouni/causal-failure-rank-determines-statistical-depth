module

public import Paid.RootD27Endpoint_LoopFrame_024
public import Paid.RootD27Endpoint_CachePrefix_030

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- SAME actual loop witness returns the original cache and preserves
the real prepared-input memory below the callee workspace. -/
theorem loop_cache_actual_region (P : Parameters) (program : Program) (input : List Cell)
    (base E returnPC testPC bodyPC exitPC : ℕ) (separated : base+48≤E)
    (testFetch : FetchesCode program testPC (rowTestCode bodyPC exitPC))
    (bodyFetch : FetchesCode program bodyPC (rowBodyCode testPC))
    (returnFetch : FetchesCode program exitPC returnCode)
    (fuel m : ℕ) (before : State) (values : ℕ→Cell)
    (position : before.pc=testPC) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (invariant : EndpointValues P E returnPC m values)
    (stored : StoredCache P E m before) (remaining : m+fuel=P.certificate.M+1) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2370*fuel+360 ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural E ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      StoredCache P E (P.certificate.M+1) after ∧ after.output=before.output ∧ BelowBase before after base ∧
      (∀ state∈trace,RegionMemory before state (endpointLoopRegion base E P.certificate.M)) := by
  induction fuel generalizing m before values with
  | zero =>
    have finished : m=P.certificate.M+1 := by omega
    have outside : ¬m≤P.certificate.M := by omega
    obtain ⟨testTrace,tested,th,tl,tc,tt,testedPC,testedFresh,testedHeader,testMemory⟩:=
      rowTest_actual program input before base m P.certificate.M bodyPC exitPC values header fresh
        invariant.counter invariant.stop (by rw [position];exact testFetch)
    have exit : tested.pc=exitPC := by simpa only [ite_eq_right outside] using testedPC
    have unchanged:=testMemory tested (trace_last_member testTrace tested tl)
    obtain ⟨returnTrace,after,rh,rl,rc,rt,afterPC,afterFresh,afterOld,afterAddress,afterIndex,returnMemory⟩:=
      return_actual program input tested base E P.certificate.M returnPC values testedHeader testedFresh
        invariant.cache invariant.stop invariant.ret (by rw [exit];exact returnFetch)
    have finalMemory:=returnMemory after (trace_last_member returnTrace after rl)
    have storedTest : StoredCache P E (P.certificate.M+1) tested := by
      rw [←finished]
      exact stored.congr unchanged.1 unchanged.2.1
    have joined:=joinTrace_spec program input testTrace returnTrace before tested after
      135 225 th tl rh rl tc rc tt rt
    refine ⟨joinTrace testTrace returnTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
      afterPC,afterFresh,afterOld,afterAddress,afterIndex,
      storedTest.congr finalMemory.1 finalMemory.2.1,finalMemory.2.2.trans unchanged.2.2,
      (BelowBase.of_unchanged base unchanged.1 unchanged.2.1).trans
        (BelowBase.of_unchanged base finalMemory.1 finalMemory.2.1),?_⟩
    exact RegionMemory.join_trace testTrace returnTrace before tested _ tl
      (fun state member => RegionMemory.of_unchanged _ (testMemory state member).1
        (testMemory state member).2.1 (testMemory state member).2.2)
      (fun state member => RegionMemory.of_unchanged _ (returnMemory state member).1
        (returnMemory state member).2.1 (returnMemory state member).2.2)
  | succ fuel ih =>
    have inside : m≤P.certificate.M := by omega
    obtain ⟨testTrace,tested,th,tl,tc,tt,testedPC,testedFresh,testedHeader,testMemory⟩:=
      rowTest_actual program input before base m P.certificate.M bodyPC exitPC values header fresh
        invariant.counter invariant.stop (by rw [position];exact testFetch)
    have bodyPosition : tested.pc=bodyPC := by simpa only [ite_eq_left inside] using testedPC
    have unchanged:=testMemory tested (trace_last_member testTrace tested tl)
    obtain ⟨bodyTrace,bodyAfter,bh,bl,bc,bt,bodyPC',bodyFresh,bodyHeader,bodyInvariant,bodyStored,bodyOutput,bodyFrame,bodyPrefixes⟩:=
      EndpointValues.actual_body_cache_region P m program input tested base E returnPC testPC values
        testedHeader testedFresh invariant (stored.congr unchanged.1 unchanged.2.1) separated
        (by rw [bodyPosition];exact bodyFetch)
    obtain ⟨later,after,lh,ll,lc,lt,afterPC,afterFresh,afterOld,afterAddress,afterIndex,afterStored,afterOutput,laterFrame,laterPrefixes⟩:=
      ih (m:=m+1) (before:=bodyAfter) (values:=bodyValues P values m) bodyPC' bodyHeader bodyFresh
        bodyInvariant bodyStored (by omega)
    have first:=joinTrace_spec program input testTrace bodyTrace before tested bodyAfter
      135 2235 th tl bh bl tc bc tt bt
    have joined:=joinTrace_spec program input (joinTrace testTrace bodyTrace) later before bodyAfter after
      2370 (2370*fuel+360) first.1 first.2.1 lh ll first.2.2.1 lc first.2.2.2 lt
    refine ⟨joinTrace (joinTrace testTrace bodyTrace) later,after,joined.1,joined.2.1,joined.2.2.1,?_,
      afterPC,afterFresh,afterOld,afterAddress,afterIndex,afterStored,
      afterOutput.trans (bodyOutput.trans unchanged.2.2),
      (BelowBase.of_unchanged base unchanged.1 unchanged.2.1).trans (bodyFrame.trans laterFrame),?_⟩
    · exact joined.2.2.2.trans_eq (loop_budget_succ fuel)
    · have testPrefixes : ∀ state∈testTrace,RegionMemory before state (endpointLoopRegion base E P.certificate.M) :=
        fun state member => RegionMemory.of_unchanged _ (testMemory state member).1
          (testMemory state member).2.1 (testMemory state member).2.2
      have bodyPrefixes' : ∀ state∈bodyTrace,RegionMemory tested state (endpointLoopRegion base E P.certificate.M) :=
        fun state member => (bodyPrefixes state member).enlarge
          (endpointRowRegion_subset_loop base E m P.certificate.M inside)
      have firstPrefixes := RegionMemory.join_trace testTrace bodyTrace before tested _ tl testPrefixes bodyPrefixes'
      exact RegionMemory.join_trace (joinTrace testTrace bodyTrace) later before bodyAfter _ first.2.1
        firstPrefixes laterPrefixes

theorem full_loop_original_cache_region (P : Parameters) (program : Program) (input : List Cell)
    (base E returnPC testPC bodyPC exitPC : ℕ) (separated : base+48≤E)
    (testFetch : FetchesCode program testPC (rowTestCode bodyPC exitPC))
    (bodyFetch : FetchesCode program bodyPC (rowBodyCode testPC))
    (returnFetch : FetchesCode program exitPC returnCode)
    (before : State) (values : ℕ→Cell) (position : before.pc=testPC)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (invariant : EndpointValues P E returnPC 0 values) (stored : StoredCache P E 0 before) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2370*(P.certificate.M+1)+360 ∧ after.pc=returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural E ∧ after.register .index=.natural (2*P.certificate.M+3) ∧
      HeapList after E (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output ∧
      BelowBase before after base ∧
      (∀ state∈trace,RegionMemory before state (endpointLoopRegion base E P.certificate.M)) := by
  obtain ⟨trace,after,head,last,chain,cost,pc,nextFresh,old,address,index,storedAfter,output,frame,prefixes⟩:=
    loop_cache_actual_region P program input base E returnPC testPC bodyPC exitPC separated testFetch bodyFetch returnFetch
      (P.certificate.M+1) 0 before values position header fresh invariant stored (by omega)
  exact ⟨trace,after,head,last,chain,cost,pc,nextFresh,old,address,index,storedAfter.original_codec,output,frame,prefixes⟩

theorem endpointLoopRegion_card_le (base E M : ℕ) :
    (endpointLoopRegion base E M).card≤48+(2*M+3) := by
  have width (pointer count : ℕ) : (cellRegion pointer count).card≤count := by
    unfold cellRegion
    exact Finset.card_image_le.trans (by simp)
  exact (Finset.card_union_le (cellRegion base headerWords) (cellRegion E (2*M+3))).trans
    (Nat.add_le_add (width base headerWords) (width E (2*M+3)))

theorem endpoint_loop_workingCells (before after : State) (base E M : ℕ)
    (memory : RegionMemory before after (endpointLoopRegion base E M)) :
    workingCells after≤workingCells before+(2*M+51) := by
  have card:=endpointLoopRegion_card_le base E M
  have cells:=memory.workingCells_le
  omega

end RootD27.Endpoint
