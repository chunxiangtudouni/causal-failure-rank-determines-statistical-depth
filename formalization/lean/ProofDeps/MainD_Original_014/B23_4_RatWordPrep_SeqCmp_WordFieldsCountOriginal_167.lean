module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsOriginal_089
public import B23_4_RatWordPrep_SeqCmp_WordFieldsCountTail_166
public import B23_4_RatWordPrep_SeqCmp_ChannelsCountOriginal_161

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFields.Count

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

noncomputable def originalHeadWork (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  RawGetter.time target+(3*RatInput.Encoder.fieldSize target+14)+RawNat.time word.1+
    (3*(PSTRTMNatValue017.rawPayload word.1).length+6)+
    (2*Channels.Count.originalAllowance (.halt : Channels.Statement C) E target word+
      6*(PSTRTMNatValue017.rawPayload word.1).length+20)
noncomputable def originalAllowance (caller : Statement C) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  Channels.Count.originalAllowance (.halt : Channels.Statement C) E target word+
    pushCap caller*(originalHeadWork (C:=C) E target word+readWork (symbolValues E word))
noncomputable def originalBudget (caller : Statement C) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  Channels.Count.originalBudget (.halt : Channels.Statement C) E target word+
    originalHeadWork (C:=C) E target word+loopBudget (symbolValues E word) (originalAllowance caller E target word)

/-- ORIGINAL wordInput, with no prepared packet/count/cursor/word-list
premise, physically produces the table, target and every word symbol in
one fixed source. This is the data-production prefix for the lookup and
arithmetic loop, not yet the complete WordOutput program. -/
theorem actual_original (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (run : Segment caller (entry context (wordInput E target word)) final)
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
        final.stk 12=[] ∧ final.stk 13=[] ∧ final.stk 14=[]) ∧
      RatInput.occupied final.stk≤originalAllowance caller E target word ∧
      run.trace.length≤originalBudget caller E target word := by
  obtain ⟨prefixFinal,prefixRun,_prefixDigits,active,contextEq,alphabet,prior,table,cursor,
    _counter,_zero,_width,_left,scratch,owned,prefixMass,prefixTime⟩ := Channels.Count.actual_original .halt context E target word
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
    counterFinal,zeroFinal,widthFinal,leftFinal,scratchFinal,frame,tailMass,tailTime⟩ :=
    actual_tail caller prefixState target (symbolValues E word) atTarget owned.2.1 scratch stream
  have headBound : headWork prefixState target (symbolValues E word)≤originalHeadWork (C:=C) E target word := by
    have a := RatInput.Encoder.point_mass prefixState.stk 10
    have b := RatInput.Encoder.point_mass prefixState.stk 11
    have mass : RatInput.occupied prefixState.stk≤Channels.Count.originalAllowance (.halt : Channels.Statement C) E target word := prefixMass
    unfold headWork originalHeadWork
    rw [symbol_count]
    omega
  have allowanceBound : tailAllowance caller prefixState target (symbolValues E word)≤originalAllowance caller E target word := by
    unfold tailAllowance originalAllowance
    exact Nat.add_le_add prefixMass (Nat.mul_le_mul_left _ (Nat.add_le_add_right headBound _))
  have loopBound : loopBudget (symbolValues E word) (tailAllowance caller prefixState target (symbolValues E word))≤
      loopBudget (symbolValues E word) (originalAllowance caller E target word) := by
    unfold loopBudget
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right allowanceBound 1)) _) _
  have paidTail : tailRun.trace.length≤originalHeadWork (C:=C) E target word+
      loopBudget (symbolValues E word) (originalAllowance caller E target word) := by
    exact tailTime.trans (Nat.add_le_add headBound loopBound)
  let whole := front.append tailRun
  have framed (slot : RatInput.Stack) (safe : TailFrame slot) : final.stk slot=prefixFinal.stk slot := frame slot safe
  refine ⟨final,whole,finalDigits,atDone,?_,?_,?_,?_,?_,symbols,cursorFinal,counterFinal,zeroFinal,?_,leftFinal,scratchFinal,?_,tailMass.trans allowanceBound,?_⟩
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
  · have total := append_length_le front tailRun
    have frontTime : front.trace.length≤Channels.Count.originalBudget (.halt : Channels.Statement C) E target word := by
      simpa only [front,List.length_map] using prefixTime
    change (front.append tailRun).trace.length≤_
    unfold originalBudget
    omega

end B23_4_RatWordPrep.WordFields.Count
