module

public import B23_4_RatWordPrep_SeqCmp_LookupCountRestore_175
public import B23_4_RatWordPrep_SeqCmp_LookupSelected_098

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def selectedWork (front : List Rat) (x : Rat) : Nat := 6*RatInput.Encoder.fieldSize x+28+restoreWork front.reverse

theorem actual_selected (truth : Bool) (caller : Statement C) (front : List Rat) (before : State C)
    (x : Rat) (tableTail oddsTail : List Bool) (active : before.l=some (.copy 0))
    (scratch : before.stk 4=[]) (empty13 : before.stk 13=[])
    (table : before.stk 2=RatInput.Encoder.packet x tableTail)
    (archive : before.stk 15=PacketLists.rats front.reverse (false::oddsTail)) :
    ∃ (final : State C) (run : Segment truth caller before final),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 2=PacketLists.rats front (RatInput.Encoder.packet x tableTail) ∧
      final.stk 15=RatInput.Encoder.packet x oddsTail ∧ final.stk 13=[] ∧ final.stk 4=[] ∧
      (∀ slot,SelectedFrame slot→final.stk slot=before.stk slot) ∧ run.trace.length≤selectedWork front x := by
  obtain ⟨copied,copyRun,copyPort,copyContext,copyContents,copyTime⟩ := actual_packet truth caller
    copyLabel RootB234.RatPacketTransport.Public.copy2To13Roles true before x tableTail active table scratch
      (by intro point different; simp only [copyLabel,different,ite_false,program]; rfl)
  have copyScratch : copied.stk 4=[] := by rw [copyContents]; rfl
  have copyTable : copied.stk 2=RatInput.Encoder.packet x tableTail := by rw [copyContents]; rfl
  have copy13 : copied.stk 13=RatInput.Encoder.packet x [] := by
    rw [copyContents]
    change RatInput.Encoder.packet x (before.stk 13)=_
    rw [empty13]
  have copyArchive : copied.stk 15=PacketLists.rats front.reverse (false::oddsTail) := by
    rw [copyContents]
    exact archive
  have copyFrame (slot : RatInput.Stack) (n2 : slot≠2) (n4 : slot≠4) (n13 : slot≠13) :
      copied.stk slot=before.stk slot := by
    rw [copyContents]
    change (if slot=2 then _ else if slot=4 then _ else if slot=13 then _ else before.stk slot)=_
    simp only [n2,n4,n13,ite_false]
  obtain ⟨restored,restoreRun,restorePort,restoreContext,restoreArchive,restoreTable,restoreScratch,restoreFrame,restoreTime⟩ :=
    actual_restore truth caller front.reverse copied oddsTail copyPort copyScratch copyArchive
  have restored13 : restored.stk 13=RatInput.Encoder.packet x [] :=
    (restoreFrame 13 (by decide)).trans copy13
  obtain ⟨final,selectedRun,finalPort,selectedContext,selectedContents,selectedTime⟩ := actual_packet truth caller
    selectedLabel RootB234.RatPacketTransport.Public.move13To15Roles false restored x []
      restorePort restored13 restoreScratch
      (by intro point different; simp only [selectedLabel,different,ite_false,program]; rfl)
  have selectedFrame (slot : RatInput.Stack) (n13 : slot≠13) (n4 : slot≠4) (n15 : slot≠15) :
      final.stk slot=restored.stk slot := by
    rw [selectedContents]
    change (if slot=13 then _ else if slot=4 then _ else if slot=15 then _ else restored.stk slot)=_
    simp only [n13,n4,n15,ite_false]
  let whole := (copyRun.append restoreRun).append selectedRun
  refine ⟨final,whole,finalPort,selectedContext.trans (restoreContext.trans copyContext),?_,?_,?_,?_,?_,?_⟩
  · rw [selectedFrame 2 (by decide) (by decide) (by decide),restoreTable,List.reverse_reverse,copyTable]
  · rw [selectedContents]
    change RatInput.Encoder.packet x (restored.stk 15)=_
    rw [restoreArchive]
  · rw [selectedContents]; rfl
  · rw [selectedContents]; rfl
  · intro slot safe
    exact (selectedFrame slot safe.2.2.1 safe.2.1 safe.2.2.2).trans
      ((restoreFrame slot ⟨safe.1,safe.2.1,safe.2.2.2⟩).trans
        (copyFrame slot safe.1 safe.2.1 safe.2.2.1))
  · have j2 := append_length_le copyRun restoreRun
    have j3 := append_length_le (copyRun.append restoreRun) selectedRun
    change ((copyRun.append restoreRun).append selectedRun).trace.length≤_
    unfold selectedWork
    omega

end B23_4_RatWordPrep.Lookup.Count
