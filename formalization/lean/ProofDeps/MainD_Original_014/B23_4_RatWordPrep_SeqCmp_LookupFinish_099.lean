module

public import B23_4_RatWordPrep_SeqCmp_LookupPhase_097
public import B23_4_RatWordPrep_SeqCmp_LookupSelected_098

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

instance skipFrameDecidable (slot : RatInput.Stack) : Decidable (SkipFrame slot) := by
  unfold SkipFrame
  infer_instance

def LookupFrame (slot : RatInput.Stack) : Prop :=
  slot≠2 ∧ slot≠4 ∧ slot≠10 ∧ slot≠11 ∧ slot≠13 ∧ slot≠15

instance lookupFrameDecidable (slot : RatInput.Stack) : Decidable (LookupFrame slot) := by
  unfold LookupFrame
  infer_instance

/-- Finish either row's lookup using the actual query0 natural packet.
Earlier rows have already been physically archived above FALSE; they are
restored together with the query prefix before the selected value returns. -/
theorem actual_finish (truth : Bool) (caller : Statement C) (earlier front : List Rat)
    (before : State C) (x : Rat) (queryTail tableTail oddsTail : List Bool)
    (active : before.l=some (.buildJ 0)) (scratch : before.stk 4=[]) (empty13 : before.stk 13=[])
    (query : before.stk 0=NatField.packet front.length queryTail)
    (table : before.stk 2=PacketLists.rats front (RatInput.Encoder.packet x tableTail))
    (archive : before.stk 15=PacketLists.rats earlier.reverse (false::oddsTail)) :
    ∃ (final : State C) (_run : Segment truth caller before final),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 2=PacketLists.rats (earlier++front) (RatInput.Encoder.packet x tableTail) ∧
      final.stk 15=RatInput.Encoder.packet x oddsTail ∧ final.stk 13=[] ∧ final.stk 4=[] ∧
      ∀ slot,LookupFrame slot→final.stk slot=before.stk slot := by
  obtain ⟨middle,phaseRun,_digits,port,phaseContext,phaseTable,phaseArchive,
    _counter,_zero,_width,_left,phaseScratch,phaseFrame⟩ := actual_phase truth false caller front
      before queryTail (RatInput.Encoder.packet x tableTail) active scratch query table
  have temp13 : middle.stk 13=[] := (phaseFrame 13 (by decide)).trans empty13
  have wholeArchive : middle.stk 15=PacketLists.rats (earlier++front).reverse (false::oddsTail) := by
    rw [phaseArchive,archive,List.reverse_append,PacketLists.rats_append]
  obtain ⟨final,selectedRun,finalPort,selectedContext,finalTable,selected,final13,finalScratch,selectedFrame⟩ :=
    actual_selected truth caller (earlier++front) middle x tableTail oddsTail port phaseScratch temp13 phaseTable wholeArchive
  let whole := phaseRun.append selectedRun
  refine ⟨final,whole,finalPort,selectedContext.trans phaseContext,finalTable,selected,final13,finalScratch,?_⟩
  intro slot safe
  exact (selectedFrame slot ⟨safe.1,safe.2.1,safe.2.2.2.2.1,safe.2.2.2.2.2⟩).trans
    (phaseFrame slot ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2.1,safe.2.2.2.2.2⟩)

end B23_4_RatWordPrep.Lookup
