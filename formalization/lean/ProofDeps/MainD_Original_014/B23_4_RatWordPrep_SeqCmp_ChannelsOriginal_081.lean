module

public import B23_4_RatWordPrep_SeqCmp_ChannelsLoop_079
public import B23_4_RatWordPrep_SeqCmp_ChannelsBuild_080

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Channels

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

instance loopFrameDecidable (slot : RatInput.Stack) : Decidable (LoopFrame slot) := by
  unfold LoopFrame
  infer_instance

def channelValues (E : BinaryExperiment) : List Rat :=
  [false,true].flatMap (fun truth => (List.finRange E.alphabetSize).map (fun symbol => E.channel truth symbol))

def afterChannels (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : List Bool :=
  (Datum.rational target::rawWord E word).flatMap encodeDatum

theorem channel_count (E : BinaryExperiment) : (channelValues E).length=2*E.alphabetSize := by
  simp [channelValues,Nat.two_mul]

theorem afterFee_split (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    OriginalFee.afterFee E target word=fields (channelValues E)++afterChannels E target word := by
  have channels : [false,true].flatMap (fun truth => (List.finRange E.alphabetSize).map
      (fun symbol => Datum.rational (E.channel truth symbol)))=(channelValues E).map Datum.rational := by
    simp only [channelValues,List.map_flatMap,List.map_map,Function.comp_def]
  have dataSplit : (PSTRTMWordFrontCode213.wordData E target word).drop 3=
      [false,true].flatMap (fun truth => (List.finRange E.alphabetSize).map
        (fun symbol => Datum.rational (E.channel truth symbol)))++
        (Datum.rational target::rawWord E word) := by
    simp [PSTRTMWordFrontCode213.wordData,rawExperiment,List.append_assoc]
  unfold OriginalFee.afterFee
  rw [dataSplit,channels,List.flatMap_append,List.flatMap_map]
  rfl

/-- One literal original-input program executes the alphabet/prefix
lookahead, physical 2N counter construction, then all 2N actual rational
getters and packet moves. The same cyclic source terminates via its real
zero port with the original target/word cursor still in place. -/
theorem actual_original (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (_run : Segment caller (entry context (wordInput E target word)) final)
      (finalDigits : List Bool),
      final.l=some .done ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2)=context ∧
      final.stk 8=NatField.packet E.alphabetSize [] ∧
      final.stk 15=RatInput.Encoder.packet E.observationFee
        (RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne [])) ∧
      final.stk 2=archived (channelValues E) [] ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (afterChannels E target word++[true]) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧
      finalDigits.length=(false::PSTRTMNatValue017.rawPayload E.alphabetSize).length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (final.stk 7=[] ∧ final.stk 3=[] ∧ final.stk 5=[] ∧ final.stk 6=[] ∧
        final.stk 9=[] ∧ final.stk 12=[] ∧ final.stk 13=[] ∧ final.stk 14=[]) := by
  obtain ⟨prefixTrace,prefixFinal,_beforeRead,first,chain,last,_member,active,contextEq,
    alphabet,packet,tape,owned,empty,_time⟩ := OriginalPrelude.actual .halt context E target word
  have prefixPath := prelude_path caller default prefixTrace _ prefixFinal first chain last active
  let prefixState := preludeCfg default prefixFinal
  let front : Segment caller (entry context (wordInput E target word)) prefixState :=
    ⟨prefixTrace.map (preludeCfg default),prefixPath.1,prefixPath.2.1,prefixPath.2.2⟩
  have atBuild : prefixState.l=some (.build 0) := by
    change prefixFinal.l.map preludeLabel=_
    rw [active]
    rfl
  obtain ⟨loopEntry,buildRun,atRound,buildContext,counter,left,scratch,buildFrame,_buildTime⟩ :=
    actual_build caller prefixState E.alphabetSize [] atBuild alphabet owned.2.2.1
  have count : PSTRTMIncrement009.valueDigits (false::PSTRTMNatValue017.rawPayload E.alphabetSize)=
      (channelValues E).length :=
    (RootB234.RuntimeCounter.Round.Public.twice_value E.alphabetSize).trans (channel_count E).symm
  have stream : ListBlank.mk (loopEntry.stk 0)=
      ListBlank.mk (fields (channelValues E)++afterChannels E target word++[true]) := by
    rw [buildFrame 0 (by decide) (by decide) (by decide)]
    have rightTape := congrArg Tape.right₀ tape
    simp only [Tape.mk₂,Tape.mk'_right₀] at rightTape
    rw [afterFee_split] at rightTape
    exact rightTape
  obtain ⟨final,loopRun,finalDigits,atDone,loopContext,priorPacket,table,cursor,
    finalCounter,zero,width,finalLeft,finalScratch,loopFrame⟩ :=
    actual_loop caller (channelValues E) loopEntry _ (afterChannels E target word)
      atRound counter left scratch count stream
  let whole := (front.append buildRun).append loopRun
  have baseEq : final.var.2=prefixFinal.var := loopContext.trans buildContext
  have framed (slot : RatInput.Stack) (safe : LoopFrame slot) : final.stk slot=prefixFinal.stk slot :=
    (loopFrame slot safe).trans (buildFrame slot safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.1)
  refine ⟨final,whole,finalDigits,atDone,?_,?_,?_,?_,cursor,finalCounter,zero,width,finalLeft,finalScratch,?_⟩
  · exact (congrArg (fun memory => OriginalFee.context (OriginalPrelude.feeMemory memory)) baseEq).trans contextEq
  · exact (framed 8 (by decide)).trans alphabet
  · exact priorPacket.trans ((buildFrame 15 (by decide) (by decide) (by decide)).trans packet)
  · rw [table,buildFrame 2 (by decide) (by decide) (by decide)]
    change archived (channelValues E) (prefixFinal.stk 2)=archived (channelValues E) []
    rw [empty 2 (Or.inl rfl)]
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (framed 7 (by decide)).trans owned.1
    · exact (framed 3 (by decide)).trans owned.2.1
    · exact (framed 5 (by decide)).trans owned.2.2.2.1
    · exact (framed 6 (by decide)).trans owned.2.2.2.2.1
    · exact (framed 9 (by decide)).trans (empty 9 (Or.inr (Or.inl rfl)))
    · exact (framed 12 (by decide)).trans owned.2.2.2.2.2.1
    · exact (framed 13 (by decide)).trans owned.2.2.2.2.2.2.1
    · exact (framed 14 (by decide)).trans owned.2.2.2.2.2.2.2

end B23_4_RatWordPrep.Channels
