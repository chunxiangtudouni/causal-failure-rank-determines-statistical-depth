module

public import Paid.PDCompute_CorePreludePC_Entry_007
public import Paid.PDLower_CalibrationCompute_CallerEmbedding_073

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDCompute.CorePreludePC

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute

attribute [local irreducible] kernel

/-- The kernel's real four-block entry does not require a disjoint old
live heap, a supplied header, an initial row or any successful-run oracle.
It writes all sixteen header cells and the original output count itself. -/
theorem head_entry (origin : ℕ) (P : Parameters) (input : List Cell)
    (base : ℕ) (before : State)
    (position : before.pc = labelAddress origin .enter)
    (fresh : before.register .fresh = .natural base)
    (M : before.register .total = .natural P.certificate.M)
    (gamma : before.register .value = .rational P.certificate.gamma) :
    EntrySegment origin input before (headResult origin P base before) := by
  let saved : State := {prologueResult before base with pc := labelAddress origin .enterBases}
  let based : State := {enterBasesResult saved base P.certificate.M with pc := labelAddress origin .enterCache}
  let counted : State := {enterCacheResult based base P.certificate.M (resultBase base P.certificate.M) with
    pc := labelAddress origin .enterBias}
  have fs : saved.register .fresh = .natural base := by
    simpa only [saved,prologue_base] using fresh
  have ms : saved.register .total = .natural P.certificate.M := by
    simpa [saved,prologueResult,storeSlotResult,State.set] using M
  have fb : based.register .fresh = .natural base := by
    simpa only [based,enterBases_fresh] using fs
  have fc : counted.register .fresh = .natural base := by
    simpa only [counted,enterCache_fresh] using fb
  have sizeLive : base+2 ∈ based.live := by
    simp [based,enterBasesResult,storeSlotResult,saved,prologueResult,State.set]
  have sizeValue : based.heap (base+2) = .natural P.certificate.M := by
    simpa [based,enterBasesResult,storeSlotResult,saved,prologueResult,State.set] using M
  have cursorLive : base+15 ∈ based.live := by
    simp [based,enterBasesResult,storeSlotResult]
  have cursorValue : based.heap (base+15) = .natural (resultBase base P.certificate.M) := by
    simp [based,enterBasesResult,storeSlotResult]
  have gammaLive : base+4 ∈ counted.live := by
    simp [counted,enterCacheResult,loadSlotResult,storeSlotResult,writeCell,based,enterBasesResult,
      saved,prologueResult,State.set]
  have gammaValue : counted.heap (base+4) = .rational P.certificate.gamma := by
    have avoid : base+4 ≠ resultBase base P.certificate.M := by unfold resultBase rowWidth; omega
    simpa [counted,enterCacheResult,loadSlotResult,storeSlotResult,writeCell,
      based,enterBasesResult,saved,prologueResult,State.set,avoid] using gamma
  have one := enter_segment origin input base before position fresh
  have two := scoped_go origin .enterBases .enterCache input saved
    (enterBasesResult saved base P.certificate.M) rfl (enterBases_execute input saved base _ fs ms) rfl
  have three := scoped_go origin .enterCache .enterBias input based
    (enterCacheResult based base P.certificate.M (resultBase base P.certificate.M)) rfl
    (enterCache_execute input based base _ _ fb sizeLive sizeValue cursorLive cursorValue) rfl
  have four := scoped_go origin .enterBias .levelGate input counted
    (enterBiasResult counted base P.certificate.gamma) rfl
    (enterBias_execute input counted base _ fc gammaLive gammaValue) rfl
  exact ((one.append_scoped two).append_scoped three).append_scoped four


private theorem kernel_words_actual : (labels.map blockLength).sum=427 := by decide

/-- The entire original functional callee, with the genuine entry count
and full PC scope retained on the SAME actual fetched trace. -/
theorem calibration_correct_pc (P : Parameters) (base endpoints : ℕ) (input : List Cell) (before : State)
    (arguments : CallArguments P base endpoints 743 before)
    (endpointHeap : HeapList before endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (separate : ∀ offset<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+offset∉workspace base P.certificate.M) (position : before.pc=316) :
    ∃ (states : List State) (after : State),states.head?=some before ∧ states.getLast?=some after ∧
      states.IsChain (fun first later=>step (locatedBlock 316 (kernel 316)) input first=some later) ∧
      Return P base 743 before after ∧
      (∀ state∈states,316≤state.pc ∧ state.pc≤743) ∧
      (∀ state∈states.dropLast,316≤state.pc ∧ state.pc<743) ∧ entryCount 316 states=1 := by
  have entryPosition : before.pc=labelAddress 316 .enter:=by
    change before.pc=316
    exact position
  let started:=headResult 316 P base before
  let header:=Header.initial base endpoints 743 P.certificate.M P.certificate.Q P.certificate.gamma
  obtain ⟨_oldHead,represented,pc,startedFresh,headOutput⟩:=
    head_correct 316 input P base endpoints 743 before arguments entryPosition
  have headRun:=head_entry 316 P input base before entryPosition arguments.fresh arguments.total arguments.value
  have headFrame : Frame before started base P.certificate.M:=headResult_frame 316 P base before
  have headEndpoints : HeapList started endpoints (encodeList encodeEndpoint P.endpointCache.toList):=
    endpointHeap.memoryFrame _ headFrame separate
  have ready : OuterReady P base endpoints 743 0 header started:=by
    refine ⟨represented,rfl,rfl,rfl,rfl,rfl,rfl,?_,startedFresh,headEndpoints,?_⟩
    · simp only [header,Header.initial,calibrationPrefix_zero,List.length_cons,List.length_nil]
    · exact headResult_cache 316 P base before
  obtain ⟨after,extra,outerRun,returnPCValue,finalFresh,finalOld,finalAddress,finalIndex,cache,output,completion,outerFrame⟩:=
    outerLoop_pc P 316 base endpoints 743 0 input started header ready pc (Nat.zero_le _) (by decide) separate
  have complete:=headRun.append_scoped outerRun
  obtain ⟨states,head,last,chain,lower,count⟩:=complete
  have correct : Return P base 743 before after:=by
    refine ⟨returnPCValue,finalFresh,finalOld,finalAddress,finalIndex,cache,?_,headFrame.trans outerFrame⟩
    rw [output,headOutput,List.append_assoc]
    rw [calibrationPrefix_zero] at completion
    rw [completion]
  have length : (kernel 316).size=427:=(kernel_size 316).trans kernel_words_actual
  have proper : ∀ state∈states.dropLast,316≤state.pc ∧ state.pc<743:=by
    intro state member
    have scope:=located_chain_scope 316 (kernel 316) input states chain state member
    rw [length] at scope
    exact ⟨scope.1,by omega⟩
  have all : ∀ state∈states,316≤state.pc ∧ state.pc≤743:=by
    intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with earlier|terminal
    · have bounded:=proper state earlier
      exact ⟨bounded.1,bounded.2.le⟩
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact ⟨lower after (List.mem_of_getLast? last),returnPCValue.le⟩
  exact ⟨states,after,head,last,chain,correct,all,proper,count⟩

/-- Stable minimal FirstExit ABI for transferring the frozen 119 numeric
callee to this exact actual trace. All original caller premises remain. -/
theorem calibration_functional_pc (P : Parameters) (base endpoints : ℕ) (input : List Cell) (before : State)
    (arguments : CallArguments P base endpoints 743 before)
    (endpointHeap : HeapList before endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (separate : ∀ offset<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+offset∉workspace base P.certificate.M) (position : before.pc=316) :
    ∃ (states : List State) (after : State),states.head?=some before ∧ states.getLast?=some after ∧
      states.IsChain (fun first later=>step (locatedBlock 316 (kernel 316)) input first=some later) ∧
      after.pc=743 ∧ (∀ state∈states,316≤state.pc ∧ state.pc≤743) ∧
      (∀ state∈states.dropLast,316≤state.pc ∧ state.pc<743) ∧ entryCount 316 states=1 := by
  obtain ⟨states,after,head,last,chain,correct,scope,proper,count⟩:=
    calibration_correct_pc P base endpoints input before arguments endpointHeap separate position
  exact ⟨states,after,head,last,chain,correct.1,scope,proper,count⟩

end PDCompute.CorePreludePC
