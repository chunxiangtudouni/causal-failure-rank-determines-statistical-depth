module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsTail_088

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFields

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

def symbolValues (E : BinaryExperiment) (word : E.StoppedWord) : List Nat :=
  (List.finRange word.1).map (fun position => (word.2 position).val)

theorem symbol_count (E : BinaryExperiment) (word : E.StoppedWord) : (symbolValues E word).length=word.1 := by
  simp only [symbolValues,List.length_map,List.length_finRange]

theorem afterChannels_split (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    Channels.afterChannels E target word=encodeDatum (.rational target)++
      encodeDatum (.natural word.1)++fields (symbolValues E word) := by
  unfold Channels.afterChannels rawWord fields symbolValues
  simp only [List.flatMap_cons,List.flatMap_map,List.append_assoc]

/-- ORIGINAL wordInput, with no prepared packet/count/cursor/word-list
premise, physically produces the table, target and every word symbol in
one fixed source. This is the data-production prefix for the lookup and
arithmetic loop, not yet the complete WordOutput program. -/
theorem actual_original (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (_run : Segment caller (entry context (wordInput E target word)) final)
      (finalDigits : List Bool),
      final.l=some .done ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2.2)=context ∧
      final.stk 8=NatField.packet E.alphabetSize [] ∧
      final.stk 15=RatInput.Encoder.packet E.observationFee
        (RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne [])) ∧
      final.stk 2=Channels.archived (Channels.channelValues E) [] ∧
      final.stk 9=RatInput.Encoder.packet target [] ∧
      final.stk 3=archived (symbolValues E word) [] ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk [true] ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧
      finalDigits.length=(PSTRTMNatValue017.rawPayload word.1).length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (final.stk 7=[] ∧ final.stk 5=[] ∧ final.stk 6=[] ∧
        final.stk 12=[] ∧ final.stk 13=[] ∧ final.stk 14=[]) := by
  obtain ⟨prefixFinal,prefixRun,_prefixDigits,active,contextEq,alphabet,prior,table,cursor,
    _counter,_zero,_width,_left,scratch,owned⟩ := Channels.actual_original .halt context E target word
  have path := channels_path caller default prefixRun.trace _ prefixFinal
    prefixRun.first prefixRun.chain prefixRun.last active
  let prefixState := channelsCfg default prefixFinal
  let front : Segment caller (entry context (wordInput E target word)) prefixState :=
    ⟨prefixRun.trace.map (channelsCfg default),path.1,path.2.1,path.2.2⟩
  have atTarget : prefixState.l=some (.target .boot) := by
    change prefixFinal.l.map channelsLabel=_
    rw [active]
    rfl
  have stream : ListBlank.mk (prefixState.stk 0)=ListBlank.mk
      (encodeDatum (.rational target)++encodeDatum (.natural (symbolValues E word).length)++
        fields (symbolValues E word)++[true]) := by
    rw [symbol_count,←afterChannels_split]
    exact cursor
  obtain ⟨final,tailRun,finalDigits,atDone,baseEq,priorFinal,targetFinal,symbols,cursorFinal,
    counterFinal,zeroFinal,widthFinal,leftFinal,scratchFinal,frame⟩ :=
    actual_tail caller prefixState target (symbolValues E word) atTarget owned.2.1 scratch stream
  let whole := front.append tailRun
  have framed (slot : RatInput.Stack) (safe : TailFrame slot) : final.stk slot=prefixFinal.stk slot := frame slot safe
  refine ⟨final,whole,finalDigits,atDone,?_,?_,?_,?_,?_,symbols,cursorFinal,counterFinal,zeroFinal,?_,leftFinal,scratchFinal,?_⟩
  · exact (congrArg (fun memory => OriginalFee.context (OriginalPrelude.feeMemory memory)) baseEq).trans contextEq
  · exact (framed 8 (by decide)).trans alphabet
  · exact priorFinal.trans prior
  · exact (framed 2 (by decide)).trans table
  · rw [targetFinal]
    change RatInput.Encoder.packet target (prefixFinal.stk 9)=_
    rw [owned.2.2.2.2.1]
  · simpa only [symbol_count] using widthFinal
  · exact ⟨(framed 7 (by decide)).trans owned.1,
      (framed 5 (by decide)).trans owned.2.2.1,
      (framed 6 (by decide)).trans owned.2.2.2.1,
      (framed 12 (by decide)).trans owned.2.2.2.2.2.1,
      (framed 13 (by decide)).trans owned.2.2.2.2.2.2.1,
      (framed 14 (by decide)).trans owned.2.2.2.2.2.2.2⟩

end B23_4_RatWordPrep.WordFields
