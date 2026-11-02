module

public import Paid.PDROC_BitVM_Kernel_RawResources_047

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawInstruction

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

def ceiling {states : ℕ} (machine : Machine states) (logical : PaperProofs.Paid.Computation.State)
    (left right : Register) (x y : Rat) (c d : ℕ) (contents : Stack → List Bool) : ℕ :=
  NatInstruction.dataSize contents+pushCap machine left right*computeBudget logical left right x y c d

def budget {states : ℕ} (machine : Machine states) (logical : PaperProofs.Paid.Computation.State)
    (left right : Register) (x y : Rat) (c d : ℕ) (contents : Stack → List Bool) : ℕ :=
  computeBudget logical left right x y c d+64*(5*ceiling machine logical left right x y c d contents+1)+5

/-- Complete ONE finite caller: original register reads, genuine RAW
operator, three real header pops, actual canonical writeback and all
workspace cleanup. Uniform native correctness is supplied once by an
already frozen machine, not as a per-input run or an additional raw value. -/
theorem runs {states : ℕ} (machine : Machine states) (resultFn : Rat → Rat → Rat) (c d : ℕ)
    (contract : RawOp.NativeContract machine resultFn c d)
    (logical : PaperProofs.Paid.Computation.State) (target left right : Register) (x y : Rat)
    (contents : Stack → List Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftRat : logical.register left=.rational x) (rightRat : logical.register right=.rational y)
    (emptyRight : contents 0=[]) (emptyLeft : contents 24=[]) :
    ∃ (run : List (State states)) (final : State states),
      run.head?=some (before states contents) ∧
      run.IsChain (fun a b=>TM2.step (program machine target left right) a=some b) ∧
      run.getLast?=some final ∧ TM2.step (program machine target left right) final=none ∧
      final.stk (registerSlot target)=encodeCellBits (.rational (resultFn x y)) ∧
      final.stk 0=[] ∧ final.stk 24=[] ∧ final.stk 25=[] ∧ final.stk 29=[] ∧
      run.length ≤ budget machine logical left right x y c d contents ∧
      ∀ role,role ≠ 0 → role ≠ 24 → role ≠ 25 → role ≠ 29 → role ≠ registerSlot target →
        final.stk role=contents role := by
  obtain ⟨native,nativeLast,nativeHead,nativeChain,nativeEnd,nativeHalt,_nativeRegs,rightWord,
    nativeTime,occupied,nativeFrame⟩ :=
    compute_resources machine resultFn c d contract logical left right x y contents represented
      leftRat rightRat emptyRight emptyLeft
  obtain ⟨first,computed,firstHead,firstChain,firstLast,computedLabel,computedData,_computedStore,firstTime⟩ :=
    CallFamily.actual_return_trace LocalLabel (LocalStore states) (source machine target left right)
      (resume states) 0 (fun other=>(initialized states) other.val) native
      (lowerBefore states 0 contents) nativeLast nativeHead nativeChain nativeEnd nativeHalt
  have firstStart : CallFamily.cfg LocalLabel (LocalStore states) 0
      (fun other=>(initialized states) other.val) (lowerBefore states 0 contents)=before states contents := by
    rw [initialized_cfg,initial_cfg]
  rw [firstStart] at firstHead
  have rightCodec : ListBlank.mk (computed.stk 0)=ListBlank.mk (encodeBits [.rational (resultFn x y)]) := by
    rw [computedData]
    exact rightWord
  obtain ⟨padding,prefixWord⟩ := RawResult.physical_prefix [.rational (resultFn x y)] (computed.stk 0) rightCodec
  obtain ⟨header,headerLast,headerHead,headerChain,headerEnd,headerHalt,headerWord,headerTime,headerFrame⟩ :=
    RawResult.runs (.rational (resultFn x y)) padding computed.stk prefixWord
  obtain ⟨second,read,secondHead,secondChain,secondLast,readLabel,readData,_readStore,secondTime⟩ :=
    CallFamily.actual_return_trace LocalLabel (LocalStore states) (source machine target left right)
      (resume states) 1 (fun other=>computed.var other.val) header
      (lowerBefore states 1 computed.stk) headerLast headerHead headerChain headerEnd headerHalt
  let headerStart := entryState states 1 computed.var computed.stk
  have secondStart : CallFamily.cfg LocalLabel (LocalStore states) 1 (fun other=>computed.var other.val)
      (lowerBefore states 1 computed.stk)=headerStart := initialized_cfg states 1 computed.var computed.stk
  rw [secondStart] at secondHead
  have edge01 : TM2.step (program machine target left right) computed=some headerStart := by
    rcases computed with ⟨label,finiteStore,physical⟩
    change label=some (CallFamily.returnLabel LocalLabel 0) at computedLabel
    subst label
    exact advance machine target left right 0 1 rfl finiteStore physical
  have bridge01 : [computed,headerStart].IsChain (fun a b=>TM2.step (program machine target left right) a=some b) :=
    List.isChain_cons_cons.mpr ⟨edge01,List.isChain_singleton _⟩
  have frontChain := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain first computed [headerStart]
    firstLast firstChain bridge01
  have frontLast : (first++[headerStart]).getLast?=some headerStart := List.getLast?_append_cons first headerStart []
  have joined := PDROC.BitVM.Log.TwoStack.join_chain (first++[headerStart]) second headerStart
    frontChain secondChain frontLast secondHead
  have joinedLast := overlap_last (first++[headerStart]) second headerStart read frontLast secondHead secondLast
  have readWord : read.stk 0=encodeCellBits (.rational (resultFn x y))++([true]++padding) := by
    rw [readData]
    exact headerWord
  obtain ⟨writer,writerLast,writerHead,writerChain,writerEnd,writerHalt,writerCell,writer0,writer24,
    writer25,writer29,writerTime,writerFrame⟩ :=
    RawWrite.runs target (.rational (resultFn x y)) ([true]++padding) read.stk default readWord
  obtain ⟨third,returned,thirdHead,thirdChain,thirdLast,returnedLabel,returnedData,_returnedStore,thirdTime⟩ :=
    CallFamily.actual_return_trace LocalLabel (LocalStore states) (source machine target left right)
      (resume states) 2 (fun other=>read.var other.val) writer (lowerBefore states 2 read.stk)
      writerLast writerHead writerChain writerEnd writerHalt
  let writerStart := entryState states 2 read.var read.stk
  have thirdStart : CallFamily.cfg LocalLabel (LocalStore states) 2 (fun other=>read.var other.val)
      (lowerBefore states 2 read.stk)=writerStart := initialized_cfg states 2 read.var read.stk
  rw [thirdStart] at thirdHead
  have edge12 : TM2.step (program machine target left right) read=some writerStart := by
    rcases read with ⟨label,finiteStore,physical⟩
    change label=some (CallFamily.returnLabel LocalLabel 1) at readLabel
    subst label
    exact advance machine target left right 1 2 rfl finiteStore physical
  have bridge12 : [read,writerStart].IsChain (fun a b=>TM2.step (program machine target left right) a=some b) :=
    List.isChain_cons_cons.mpr ⟨edge12,List.isChain_singleton _⟩
  let beforeWriter := (first++[headerStart])++second.tail
  have beforeWriterChain := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain
    beforeWriter read [writerStart] joinedLast joined bridge12
  have beforeWriterLast : (beforeWriter++[writerStart]).getLast?=some writerStart :=
    List.getLast?_append_cons beforeWriter writerStart []
  let allCalls := (beforeWriter++[writerStart])++third.tail
  have allChain : allCalls.IsChain (fun a b=>TM2.step (program machine target left right) a=some b) :=
    PDROC.BitVM.Log.TwoStack.join_chain (beforeWriter++[writerStart]) third writerStart
      beforeWriterChain thirdChain beforeWriterLast thirdHead
  have allLast : allCalls.getLast?=some returned :=
    overlap_last (beforeWriter++[writerStart]) third writerStart returned beforeWriterLast thirdHead thirdLast
  let final : State states := ⟨none,returned.var,returned.stk⟩
  have lastEdge : TM2.step (program machine target left right) returned=some final := by
    rcases returned with ⟨label,finiteStore,physical⟩
    change label=some (CallFamily.returnLabel LocalLabel 2) at returnedLabel
    subst label
    exact finish machine target left right finiteStore physical
  have lastPair : [returned,final].IsChain (fun a b=>TM2.step (program machine target left right) a=some b) :=
    List.isChain_cons_cons.mpr ⟨lastEdge,List.isChain_singleton _⟩
  have actual := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain allCalls returned [final]
    allLast allChain lastPair
  have nativeMember : nativeLast ∈ native := List.mem_of_mem_getLast? (by rw [nativeEnd];rfl)
  have computedBound : ∀ role,(computed.stk role).length ≤ ceiling machine logical left right x y c d contents := by
    intro role
    rw [computedData]
    exact occupied nativeLast nativeMember role
  have headerBound : ∀ role,(read.stk role).length ≤ ceiling machine logical left right x y c d contents := by
    intro role
    by_cases is0 : role=0
    · subst role
      have decreases : (headerLast.stk 0).length ≤ (computed.stk 0).length := by
        rw [prefixWord,RawResult.singleton_word,headerWord]
        simp only [List.length_append,List.length_cons,List.length_nil]
        omega
      rw [readData]
      exact decreases.trans (computedBound 0)
    · rw [readData,headerFrame role is0]
      exact computedBound role
  have writerSize : RawWrite.inputSize target read.stk ≤ 5*ceiling machine logical left right x y c d contents := by
    have a := headerBound 0
    have b := headerBound 24
    have e := headerBound 25
    have f := headerBound 29
    have g := headerBound (registerSlot target)
    dsimp only [RawWrite.inputSize]
    omega
  have totalWriter : writer.length ≤ 64*(5*ceiling machine logical left right x y c d contents+1) :=
    writerTime.trans (Nat.mul_le_mul_left 64 (Nat.add_le_add_right writerSize 1))
  refine ⟨allCalls++[final],final,?_,actual,List.getLast?_append_cons allCalls final [],rfl,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [allCalls,beforeWriter,List.head?_append,firstHead,Option.some_or]
  · change returned.stk (registerSlot target)=_
    rw [returnedData]
    exact writerCell
  · change returned.stk 0=[]
    rw [returnedData]
    exact writer0
  · change returned.stk 24=[]
    rw [returnedData]
    exact writer24
  · change returned.stk 25=[]
    rw [returnedData]
    exact writer25
  · change returned.stk 29=[]
    rw [returnedData]
    exact writer29
  · have firstBound : first.length ≤ computeBudget logical left right x y c d :=
      firstTime.le.trans nativeTime
    have secondBound : second.length=2 := secondTime.trans headerTime
    have thirdBound : third.length ≤ 64*(5*ceiling machine logical left right x y c d contents+1) :=
      thirdTime.le.trans totalWriter
    simp only [allCalls,beforeWriter,List.length_append,List.length_tail,List.length_cons,List.length_nil]
    dsimp only [budget]
    omega
  · intro role not0 not24 not25 not29 notTarget
    change returned.stk role=contents role
    rw [returnedData,writerFrame role not0 not24 not25 not29 notTarget,readData,headerFrame role not0,computedData]
    exact nativeFrame role not0 not24

end PDROC.BitVM.Kernel.RawInstruction
