module

public import B23_4_RatWordPrep_SeqCmp_WordPackOriginal_109
public import B23_4_RatWordPrep_SeqCmp_WordPackCountLayout_169
public import B23_4_RatWordPrep_SeqCmp_WordFieldsCountOriginal_167

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordPack.Count

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

noncomputable def originalLayoutWork (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  2*WordFields.Count.originalAllowance (.halt : WordFields.Statement C) E target word+
    3*RatInput.Encoder.fieldSize target+3*(PSTRTMNatValue017.rawPayload E.alphabetSize).length+32+
    naturalWork (WordFields.symbolValues E word).reverse+rationalWork (Channels.channelValues E).reverse+
    2*(PacketLists.rats (Channels.channelValues E) []).length+4
noncomputable def originalBudget (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  WordFields.Count.originalBudget (.halt : WordFields.Statement C) E target word+originalLayoutWork (C:=C) E target word

def originalMass (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  (PacketLists.naturals (WordFields.symbolValues E word) []).length+
  (NatField.packet E.alphabetSize (RatInput.Encoder.packet target [])).length+
  (PacketLists.rats (Channels.channelValues E) []).length+
  (RatInput.Encoder.packet E.observationFee (RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne []))).length+
  2*(PSTRTMNatValue017.rawPayload word.1).length+4

/-- Literal ORIGINAL wordInput to the exact physical lookup/arithmetic
layout. The input word/table are read, every reordering/clear is paid,
and all temporary/arithmetic-owned slots are actually returned empty. -/
theorem actual_original (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (run : Segment caller (entry context (wordInput E target word)) final)
      (finalDigits : List Bool),
      final.l=some .done ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2.2)=context ∧
      final.stk 0=PacketLists.naturals (WordFields.symbolValues E word) [] ∧
      final.stk 1=NatField.packet E.alphabetSize (RatInput.Encoder.packet target []) ∧
      final.stk 2=PacketLists.rats (Channels.channelValues E) [] ∧
      final.stk 15=RatInput.Encoder.packet E.observationFee
        (RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne [])) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧
      finalDigits.length=(PSTRTMNatValue017.rawPayload word.1).length ∧ final.stk 11=[false] ∧
      (final.stk 3=[] ∧ final.stk 4=[] ∧ final.stk 5=[] ∧ final.stk 6=[] ∧ final.stk 7=[] ∧
        final.stk 8=[] ∧ final.stk 9=[] ∧ final.stk 12=[] ∧ final.stk 13=[] ∧ final.stk 14=[]) ∧
      RatInput.occupied final.stk=originalMass E target word ∧
      run.trace.length≤originalBudget (C:=C) E target word := by
  obtain ⟨prefixFinal,prefixRun,digits,active,contextEq,alphabet,prior,table,targetPacket,wordQueue,
    _cursor,counter,zero,width,left,scratch,owned,prefixMass,prefixTime⟩ := WordFields.Count.actual_original .halt context E target word
  have path := fields_path caller prefixRun.trace _ prefixFinal prefixRun.first prefixRun.chain prefixRun.last active
  let beforeLayout := fieldsCfg prefixFinal
  let front : Segment caller (entry context (wordInput E target word)) beforeLayout :=
    ⟨prefixRun.trace.map fieldsCfg,path.1,path.2.1,path.2.2⟩
  have atLayout : beforeLayout.l=some (.clear0 0) := by
    change prefixFinal.l.map fieldsLabel=_
    rw [active]
    rfl
  have tablePhysical : beforeLayout.stk 2=PacketLists.rats (Channels.channelValues E).reverse [] :=
    table.trans (PacketLists.channel_archive _ _)
  have wordPhysical : beforeLayout.stk 3=PacketLists.naturals (WordFields.symbolValues E word).reverse [] :=
    wordQueue.trans (PacketLists.symbol_archive _ _)
  obtain ⟨final,layoutRun,atDone,baseEq,symbols,metadata,channels,packet,empty3,empty4,empty8,empty9,empty13,frame,layoutTime⟩ :=
    actual_layout caller beforeLayout E.alphabetSize target (Channels.channelValues E) (WordFields.symbolValues E word)
      atLayout scratch owned.2.2.2.2.1 alphabet targetPacket tablePhysical wordPhysical
  let whole := front.append layoutRun
  have framed (slot : RatInput.Stack) (safe : LayoutFrame slot) : final.stk slot=prefixFinal.stk slot := frame slot safe
  refine ⟨final,whole,digits,atDone,?_,symbols,metadata,channels,packet.trans prior,?_,zero,width,?_,
    ⟨empty3,empty4,?_,?_,?_,empty8,empty9,?_,empty13,?_⟩,?_,?_⟩
  · exact (congrArg (fun memory => OriginalFee.context (OriginalPrelude.feeMemory memory)) baseEq).trans contextEq
  · exact (framed 10 (by decide)).trans counter
  · exact (framed 11 (by decide)).trans left
  · exact (framed 5 (by decide)).trans owned.2.1
  · exact (framed 6 (by decide)).trans owned.2.2.1
  · exact (framed 7 (by decide)).trans owned.1
  · exact (framed 12 (by decide)).trans owned.2.2.2.1
  · exact (framed 14 (by decide)).trans owned.2.2.2.2.2
  · have p15 := packet.trans prior
    have p10 := (framed 10 (by decide)).trans counter
    have p11 := (framed 11 (by decide)).trans left
    have p5 := (framed 5 (by decide)).trans owned.2.1
    have p6 := (framed 6 (by decide)).trans owned.2.2.1
    have p7 := (framed 7 (by decide)).trans owned.1
    have p12 := (framed 12 (by decide)).trans owned.2.2.2.1
    have p14 := (framed 14 (by decide)).trans owned.2.2.2.2.2
    simp [RatInput.occupied,Fin.sum_univ_succ,symbols,metadata,channels,p15,p10,p11,p5,p6,p7,p12,p14,
      empty3,empty4,empty8,empty9,empty13,RootB234.RuntimeCounter.Round.packet_length,width,originalMass]
    omega
  · have frontTime : front.trace.length≤WordFields.Count.originalBudget (.halt : WordFields.Statement C) E target word := by
      simpa only [front,List.length_map] using prefixTime
    have layoutBound : layoutWork beforeLayout E.alphabetSize target (Channels.channelValues E) (WordFields.symbolValues E word)≤
        originalLayoutWork (C:=C) E target word := by
      have a := RatInput.Encoder.point_mass beforeLayout.stk 0
      have b := RatInput.Encoder.point_mass beforeLayout.stk 1
      have mass : RatInput.occupied beforeLayout.stk≤WordFields.Count.originalAllowance (.halt : WordFields.Statement C) E target word := prefixMass
      unfold layoutWork originalLayoutWork
      omega
    have paidLayout := layoutTime.trans layoutBound
    have total := front.append_length_le layoutRun
    change (front.append layoutRun).trace.length≤_
    unfold originalBudget
    omega

end B23_4_RatWordPrep.WordPack.Count
