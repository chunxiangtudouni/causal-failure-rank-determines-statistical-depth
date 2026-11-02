module

public import B23_4_RatWordPrep_SeqCmp_LookupCountPhase_176
public import B23_4_RatWordPrep_SeqCmp_LookupCountSelected_177
public import B23_4_RatWordPrep_SeqCmp_LookupFinish_099

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

noncomputable def finishWork (truth : Bool) (caller : Statement C) (earlier front : List Rat) (x : Rat) (mass : Nat) : Nat :=
  phaseWork truth caller front mass+selectedWork (earlier++front) x

theorem finishWork_mono (truth : Bool) (caller : Statement C) (earlier front : List Rat) (x : Rat)
    {a b : Nat} (bound : a≤b) : finishWork truth caller earlier front x a≤finishWork truth caller earlier front x b :=
  Nat.add_le_add_right (phaseWork_mono truth caller front bound) _

/-- Finish either row's lookup using the actual query0 natural packet.
Earlier rows have already been physically archived above FALSE; they are
restored together with the query prefix before the selected value returns. -/
theorem actual_finish (truth : Bool) (caller : Statement C) (earlier front : List Rat)
    (before : State C) (x : Rat) (queryTail tableTail oddsTail : List Bool)
    (active : before.l=some (.buildJ 0)) (scratch : before.stk 4=[]) (empty13 : before.stk 13=[])
    (query : before.stk 0=NatField.packet front.length queryTail)
    (table : before.stk 2=PacketLists.rats front (RatInput.Encoder.packet x tableTail))
    (archive : before.stk 15=PacketLists.rats earlier.reverse (false::oddsTail)) :
    ∃ (final : State C) (run : Segment truth caller before final),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 2=PacketLists.rats (earlier++front) (RatInput.Encoder.packet x tableTail) ∧
      final.stk 15=RatInput.Encoder.packet x oddsTail ∧ final.stk 13=[] ∧ final.stk 4=[] ∧
      (∀ slot,LookupFrame slot→final.stk slot=before.stk slot) ∧
      (∃ digits,final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits ∧
        digits.length=(PSTRTMNatValue017.rawPayload front.length).length ∧ final.stk 11=[false]) ∧
      run.trace.length≤finishWork truth caller earlier front x (RatInput.occupied before.stk) := by
  obtain ⟨middle,phaseRun,digits,port,phaseContext,phaseTable,phaseArchive,
    counter,_zero,width,left,phaseScratch,phaseFrame,_phaseMass,phaseTime⟩ := actual_phase truth false caller front
      before queryTail (RatInput.Encoder.packet x tableTail) active scratch query table
  have temp13 : middle.stk 13=[] := (phaseFrame 13 (by decide)).trans empty13
  have wholeArchive : middle.stk 15=PacketLists.rats (earlier++front).reverse (false::oddsTail) := by
    rw [phaseArchive,archive,List.reverse_append,PacketLists.rats_append]
  obtain ⟨final,selectedRun,finalPort,selectedContext,finalTable,selected,final13,finalScratch,selectedFrame,selectedTime⟩ :=
    actual_selected truth caller (earlier++front) middle x tableTail oddsTail port phaseScratch temp13 phaseTable wholeArchive
  let whole := phaseRun.append selectedRun
  refine ⟨final,whole,finalPort,selectedContext.trans phaseContext,finalTable,selected,final13,finalScratch,?_,?_,?_⟩
  · intro slot safe
    exact (selectedFrame slot ⟨safe.1,safe.2.1,safe.2.2.2.2.1,safe.2.2.2.2.2⟩).trans
      (phaseFrame slot ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,safe.2.2.2.2.2⟩)
  · exact ⟨digits,(selectedFrame 10 (by unfold SelectedFrame; decide)).trans counter,width,
      (selectedFrame 11 (by unfold SelectedFrame; decide)).trans left⟩
  · have joined := append_length_le phaseRun selectedRun
    change (phaseRun.append selectedRun).trace.length≤_
    unfold finishWork
    omega

end B23_4_RatWordPrep.Lookup.Count
