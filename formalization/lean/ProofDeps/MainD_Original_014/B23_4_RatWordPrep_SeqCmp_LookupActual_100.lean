module

public import B23_4_RatWordPrep_SeqCmp_LookupFinish_099

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

def markedState (truth : Bool) (before : State C) : State C :=
  ⟨some (if truth then .buildN 0 else .buildJ 0),before.var,
    Function.update before.stk 15 (false::before.stk 15)⟩

theorem mark_step (truth : Bool) (caller : Statement C) (before : State C) (active : before.l=some .boot) :
    TM2.step (program truth caller) before=some (markedState truth before) := by
  cases before with
  | mk point memory slots =>
    change point=some .boot at active
    subst point
    rfl

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
    ∃ (final : State C) (_run : Segment truth caller before final),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧ final.stk 2=before.stk 2 ∧
      final.stk 15=RatInput.Encoder.packet x (before.stk 15) ∧ final.stk 13=[] ∧ final.stk 4=[] ∧
      ∀ slot,LookupFrame slot→final.stk slot=before.stk slot := by
  let marked := markedState truth before
  let marker : Segment truth caller before marked :=
    ⟨[before,marked],rfl,List.isChain_cons_cons.mpr ⟨mark_step truth caller before active,.singleton _⟩,rfl⟩
  have markFrame (slot : RatInput.Stack) (n15 : slot≠15) : marked.stk slot=before.stk slot :=
    Function.update_of_ne n15 _ _
  have markedScratch : marked.stk 4=[] := (markFrame 4 (by decide)).trans scratch
  have marked13 : marked.stk 13=[] := (markFrame 13 (by decide)).trans empty13
  have markedQuery : marked.stk 0=NatField.packet front.length queryTail := (markFrame 0 (by decide)).trans query
  cases truth with
  | false =>
    have markedTable : marked.stk 2=PacketLists.rats front (RatInput.Encoder.packet x tableTail) :=
      (markFrame 2 (by decide)).trans table
    obtain ⟨final,finishRun,port,context,finalTable,selected,final13,finalScratch,frame⟩ :=
      actual_finish false caller [] front marked x queryTail tableTail (before.stk 15)
        rfl markedScratch marked13 markedQuery markedTable rfl
    let whole := marker.append finishRun
    refine ⟨final,whole,port,context,?_,selected,final13,finalScratch,?_⟩
    · exact finalTable.trans table.symm
    · intro slot safe
      exact (frame slot safe).trans (markFrame slot safe.2.2.2.2.2)
  | true =>
    have markedTable : marked.stk 2=PacketLists.rats firstRow
        (PacketLists.rats front (RatInput.Encoder.packet x tableTail)) := by
      rw [markFrame 2 (by decide),table,PacketLists.rats_append]
      rfl
    have markedMeta : marked.stk 1=NatField.packet firstRow.length metadataTail := (markFrame 1 (by decide)).trans metadata
    obtain ⟨middle,firstRun,_digits,firstPort,firstContext,firstTable,firstArchive,
      _counter,_zero,_width,_left,firstScratch,firstFrame⟩ :=
      actual_phase true true caller firstRow marked metadataTail
        (PacketLists.rats front (RatInput.Encoder.packet x tableTail)) rfl markedScratch markedMeta markedTable
    have mid13 : middle.stk 13=[] := (firstFrame 13 (by decide)).trans marked13
    have midQuery : middle.stk 0=NatField.packet front.length queryTail :=
      (firstFrame 0 (by decide)).trans markedQuery
    obtain ⟨final,finishRun,port,finishContext,finalTable,selected,final13,finalScratch,frame⟩ :=
      actual_finish true caller firstRow front middle x queryTail tableTail (before.stk 15)
        firstPort firstScratch mid13 midQuery firstTable firstArchive
    let whole := (marker.append firstRun).append finishRun
    refine ⟨final,whole,port,finishContext.trans firstContext,finalTable.trans table.symm,
      selected,final13,finalScratch,?_⟩
    intro slot safe
    exact (frame slot safe).trans
      ((firstFrame slot ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,safe.2.2.2.2.2⟩).trans
        (markFrame slot safe.2.2.2.2.2))

end B23_4_RatWordPrep.Lookup
