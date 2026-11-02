module

public import B23_4_RatWordPrep_SeqCmp_RawNatCode_070

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.RawNat

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

variable {C : Type*}

def time (number : Nat) : Nat :=
  (PSTRTMNatValue017.rawPayload number).length^2+12*(PSTRTMNatValue017.rawPayload number).length+16

theorem shared (before : ParserState (C × PSTRSymbolicNaturalExport.Store)) (active : before.l=some 1) :
    fieldCfg (⟨some 0,parserIso C before.var,before.stk⟩ : NatField.State (C × ParserMemory))=parserCfg before := by
  cases before with
  | mk position memory contents =>
    change position=some 1 at active
    subst position
    rfl

/-- Actual current raw Natural Datum -> owned Nat packet15, with real
fresh marker/control reset/native parser/export/restore on one trace. -/
theorem actual_current (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (number : Nat) (suffix : List Bool)
    (right : ListBlank.mk (background 0)=ListBlank.mk (encodeDatum (.natural number)++suffix++[true])) :
    ∃ (trace : List (State C)) (final parsed : State C),
      trace.head?=some (entry background memory) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ parsed∈trace ∧ final.l=some .done ∧ final.var.1.1=memory.1.1 ∧
      final.stk=Function.update parsed.stk 15 (NatField.packet number (background 15)) ∧
      Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))=Tape.mk₂
        (false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::true::background 1))
        (suffix++[true]) ∧
      parsed.stk 7=background 7 ∧ parsed.stk 15=background 15 ∧ trace.length ≤ time number := by
  obtain ⟨pTrace,pFinal,pFirst,pChain,pLast,pActive,pTape,pTime,pFrames⟩:=
    actual_parser (memory.1.1,memory.2) background number suffix right
  have pPath:=parser_path caller pTrace _ pFinal pFirst pChain pLast pActive
  let pMemory:=parserIso C pFinal.var
  have physical:=finite_archive background number suffix pFinal pTape
  obtain ⟨eTrace,eFinal,eFirst,eChain,eLast,eActive,eContext,eContents,eTime⟩:=
    NatField.actual_current pMemory pFinal.stk number physical
  have ePath:=field_path caller eTrace _ eFinal eFirst eChain eLast eActive
  let boot : Segment caller (entry background memory) (parserCfg (parserEntry (memory.1.1,memory.2) background)) 2:=
    ⟨[entry background memory,parserCfg (parserEntry (memory.1.1,memory.2) background)],rfl,
      List.isChain_cons_cons.mpr ⟨boot_step caller background memory,List.isChain_singleton _⟩,rfl,by rfl⟩
  let parsedPart : Segment caller (parserCfg (parserEntry (memory.1.1,memory.2) background)) (parserCfg pFinal)
      ((PSTRTMNatValue017.rawPayload number).length^2+9*(PSTRTMNatValue017.rawPayload number).length+5):=
    ⟨pTrace.map parserCfg,pPath.1,pPath.2.1,pPath.2.2,by simpa only [List.length_map] using Nat.le_of_eq pTime⟩
  let exportPart : Segment caller (parserCfg pFinal) (fieldCfg eFinal) (3*(PSTRTMNatValue017.rawPayload number).length+6):=
    ⟨eTrace.map fieldCfg,ePath.1.trans (congrArg some (shared pFinal pActive)),ePath.2.1,ePath.2.2,
      by simpa only [List.length_map] using Nat.le_of_eq eTime⟩
  let front:=boot.append parsedPart
  let whole:=front.append exportPart
  have frame:=pFrames pFinal (List.mem_of_getLast? pLast)
  have context : (fieldCfg eFinal).var.1.1=memory.1.1 := by
    change eFinal.var.1.1=memory.1.1
    have same:=congrArg (fun v : C × ParserMemory => v.1) eContext
    change eFinal.var.1.1=pFinal.var.1.1 at same
    exact same.trans (congrArg (fun v : C × PSTRSymbolicNaturalExport.Store => v.1) frame.1)
  have contents : (fieldCfg eFinal).stk=Function.update (parserCfg pFinal).stk 15 (NatField.packet number (background 15)) := by
    change eFinal.stk=Function.update pFinal.stk 15 _
    rw [eContents,frame.2 15 (by decide) (by decide)]
  refine ⟨whole.trace,fieldCfg eFinal,parserCfg pFinal,whole.head,whole.chain,whole.last,?_,?_,context,contents,pTape,
    frame.2 7 (by decide) (by decide),frame.2 15 (by decide) (by decide),?_⟩
  · change parserCfg pFinal∈front.trace++exportPart.trace.tail
    exact List.mem_append_left _ (List.mem_of_getLast? front.last)
  · change eFinal.l.map fieldLabel=some .done
    rw [eActive]
    rfl
  · have count:=whole.count
    dsimp only [time]
    omega

end B23_4_RatWordPrep.RawNat
