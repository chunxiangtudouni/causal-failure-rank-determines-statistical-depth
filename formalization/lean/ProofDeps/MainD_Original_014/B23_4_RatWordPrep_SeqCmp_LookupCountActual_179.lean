module

public import B23_4_RatWordPrep_SeqCmp_LookupCountFinish_178

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

noncomputable def actualWork (truth : Bool) (caller : Statement C) (firstRow front : List Rat) (x : Rat) (mass : Nat) : Nat :=
  2+(if truth then phaseWork truth caller firstRow (mass+1)+
    finishWork truth caller firstRow front x (phaseMass truth caller firstRow.length (mass+1))
    else finishWork truth caller [] front x (mass+1))

/-- Runtime lookup from physical N1/query0 packets and a physical table.
The FALSE marker is pushed and popped by real source operations; every
skipped table field is restored and selected data comes from the actual
table head at the actual counter's zero return. -/
theorem actual (truth : Bool) (caller : Statement C) (firstRow front : List Rat)
    (before : State C) (x : Rat) (queryTail metadataTail tableTail : List Bool)
    (active : before.l=some .boot) (scratch : before.stk 4=[]) (empty13 : before.stk 13=[])
    (query : before.stk 0=NatField.packet front.length queryTail)
    (metadata : before.stk 1=NatField.packet firstRow.length metadataTail)
    (table : before.stk 2=PacketLists.rats ((if truth then firstRow else [])++front)
      (RatInput.Encoder.packet x tableTail)) :
    ∃ (final : State C) (run : Segment truth caller before final),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧ final.stk 2=before.stk 2 ∧
      final.stk 15=RatInput.Encoder.packet x (before.stk 15) ∧ final.stk 13=[] ∧ final.stk 4=[] ∧
      (∀ slot,LookupFrame slot→final.stk slot=before.stk slot) ∧
      (∃ digits,final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits ∧
        digits.length=(PSTRTMNatValue017.rawPayload front.length).length ∧ final.stk 11=[false]) ∧
      run.trace.length≤actualWork truth caller firstRow front x (RatInput.occupied before.stk) := by
  let marked := markedState truth before
  let marker : Segment truth caller before marked :=
    ⟨[before,marked],rfl,List.isChain_cons_cons.mpr ⟨mark_step truth caller before active,.singleton _⟩,rfl⟩
  have markFrame (slot : RatInput.Stack) (n15 : slot≠15) : marked.stk slot=before.stk slot :=
    Function.update_of_ne n15 _ _
  have markedScratch : marked.stk 4=[] := (markFrame 4 (by decide)).trans scratch
  have marked13 : marked.stk 13=[] := (markFrame 13 (by decide)).trans empty13
  have markedQuery : marked.stk 0=NatField.packet front.length queryTail := (markFrame 0 (by decide)).trans query
  have markedMass : RatInput.occupied marked.stk=RatInput.occupied before.stk+1 :=
    WordFinish.Resources.push_mass before.stk 15 false
  have markerTime : marker.trace.length=2 := rfl
  cases truth with
  | false =>
    have markedTable : marked.stk 2=PacketLists.rats front (RatInput.Encoder.packet x tableTail) :=
      (markFrame 2 (by decide)).trans table
    obtain ⟨final,finishRun,port,context,finalTable,selected,final13,finalScratch,frame,counterFinal,finishTime⟩ :=
      actual_finish false caller [] front marked x queryTail tableTail (before.stk 15)
        rfl markedScratch marked13 markedQuery markedTable rfl
    let whole := marker.append finishRun
    refine ⟨final,whole,port,context,?_,selected,final13,finalScratch,?_,counterFinal,?_⟩
    · exact finalTable.trans table.symm
    · intro slot safe
      exact (frame slot safe).trans (markFrame slot safe.2.2.2.2.2)
    · have joined := append_length_le marker finishRun
      rw [markedMass] at finishTime
      change (marker.append finishRun).trace.length≤_
      simp only [actualWork,Bool.false_eq_true,ite_false]
      omega
  | true =>
    have markedTable : marked.stk 2=PacketLists.rats firstRow
        (PacketLists.rats front (RatInput.Encoder.packet x tableTail)) := by
      rw [markFrame 2 (by decide),table,PacketLists.rats_append]
      rfl
    have markedMeta : marked.stk 1=NatField.packet firstRow.length metadataTail := (markFrame 1 (by decide)).trans metadata
    obtain ⟨middle,firstRun,_digits,firstPort,firstContext,firstTable,firstArchive,
      _counter,_zero,_width,_left,firstScratch,firstFrame,firstMass,firstTime⟩ :=
      actual_phase true true caller firstRow marked metadataTail
        (PacketLists.rats front (RatInput.Encoder.packet x tableTail)) rfl markedScratch markedMeta markedTable
    have mid13 : middle.stk 13=[] := (firstFrame 13 (by decide)).trans marked13
    have midQuery : middle.stk 0=NatField.packet front.length queryTail :=
      (firstFrame 0 (by decide)).trans markedQuery
    obtain ⟨final,finishRun,port,finishContext,finalTable,selected,final13,finalScratch,frame,counterFinal,finishTime⟩ :=
      actual_finish true caller firstRow front middle x queryTail tableTail (before.stk 15)
        firstPort firstScratch mid13 midQuery firstTable firstArchive
    let whole := (marker.append firstRun).append finishRun
    refine ⟨final,whole,port,finishContext.trans firstContext,finalTable.trans table.symm,
      selected,final13,finalScratch,?_,counterFinal,?_⟩
    · intro slot safe
      exact (frame slot safe).trans
        ((firstFrame slot ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,safe.2.2.2.2.2⟩).trans
          (markFrame slot safe.2.2.2.2.2))
    · have paidFinish := finishTime.trans (finishWork_mono true caller firstRow front x firstMass)
      rw [markedMass] at paidFinish firstTime
      have j2 := append_length_le marker firstRun
      have j3 := append_length_le (marker.append firstRun) finishRun
      change ((marker.append firstRun).append finishRun).trace.length≤_
      simp only [actualWork,ite_true]
      omega

end B23_4_RatWordPrep.Lookup.Count
