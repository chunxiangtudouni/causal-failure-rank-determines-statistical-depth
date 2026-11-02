module

public import B23_4_RatWordPrep_SeqCmp_RawCode_021

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.RawGetter

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PA17TMRatArithmeticParse002

variable {C : Type*}

def time (x : Rat) : Nat := (numeratorDigits x).length^2+(denominatorDigits x).length^2+
  12*((numeratorDigits x).length+(denominatorDigits x).length)+32

/-- Actual original rational Datum to the established signed Rat packet.
The fresh left marker and parser control initialization are paid source
operations. The packet answer and all paths are produced in this theorem. -/
theorem actual_raw_field (caller : Statement C) (background : RatInput.Stack → List Bool)
    (memory : Store C) (x : Rat) (suffix : List Bool) :
    ∃ trace : List (State C), ∃ final parsed : State C,
      trace.head?=some (entry background memory x suffix) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ parsed∈trace ∧ final.l=some .done ∧
      final.var.1.1=memory.1.1 ∧
      final.stk=Function.update parsed.stk 15 (RatInput.Encoder.packet x (background 15)) ∧
      Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))=Tape.mk₂
        (bothLeft (false::sign x::true::background 1) (numeratorDigits x) (denominatorDigits x)) suffix ∧
      parsed.stk 7=background 7 ∧ parsed.stk 15=background 15 ∧ trace.length≤time x := by
  obtain ⟨pTrace,pFinal,pFirst,pChain,pLast,pActive,pTape,pLength,pFrames⟩ :=
    actual_parser (memory.1.1,memory.2) background x suffix
  have pPath := parser_path caller pTrace _ pFinal pFirst pChain pLast pActive
  let bootState := parserCfg (parserEntry (memory.1.1,memory.2) background x suffix)
  let boot : Segment caller (entry background memory x suffix) bootState 2 :=
    ⟨[entry background memory x suffix,bootState],rfl,
      List.isChain_cons_cons.mpr ⟨boot_step caller background memory x suffix,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  let parsed := parserCfg pFinal
  let parsedPath : Segment caller bootState parsed
      ((numeratorDigits x).length^2+(denominatorDigits x).length^2+
        9*((numeratorDigits x).length+(denominatorDigits x).length)+12) :=
    ⟨pTrace.map parserCfg,pPath.1,pPath.2.1,pPath.2.2,by rw [List.length_map,pLength]⟩
  let front := boot.append parsedPath
  obtain ⟨archiveTail,archive⟩ := finite_archive background x suffix pFinal pTape
  let nr := (numeratorDigits x).reverse
  let dr := (denominatorDigits x).reverse
  have archiveParsed : parsed.stk 1=PSTRSymbolicRatExport.archive (sign x) nr dr (true::archiveTail) := archive
  let eTrace := PSTRSymbolicRatExport.ratTrace parsed.var.1 parsed.var.2.1 parsed.var.2.2.1 parsed.var.2.2.2
    (sign x) nr dr (true::archiveTail) (parsed.stk 7) (parsed.stk 15) parsed.stk
  obtain ⟨resultBit,eFirst,eChain,eLast,eLength⟩ := PSTRSymbolicRatExport.actual_rat_export
    parsed.var.1 parsed.var.2.1 parsed.var.2.2.1 parsed.var.2.2.2 (sign x) nr dr
    (true::archiveTail) (parsed.stk 7) (parsed.stk 15) parsed.stk
  let eFinal : PSTRSymbolicNaturalExport.State (C × ParserMemory) :=
    PSTRSymbolicNaturalExport.state (some 4) (parsed.var.1,(resultBit,true,parsed.var.2.2.2))
      (parsed.stk 1) (parsed.stk 7) (RatInput.Encoder.packet x (parsed.stk 15)) parsed.stk
  have eLast' : eTrace.getLast?=some eFinal := by
    rw [←archiveParsed] at eLast
    simpa only [eTrace,eFinal,nr,dr,List.reverse_reverse,RatInput.Encoder.packet] using eLast
  have eActive : eFinal.l=some 4 := rfl
  have eStart : PSTRSymbolicNaturalExport.state (some 0) parsed.var
      (PSTRSymbolicRatExport.archive (sign x) nr dr (true::archiveTail)) (parsed.stk 7) (parsed.stk 15) parsed.stk=
      (⟨some 0,parsed.var,parsed.stk⟩ : PSTRSymbolicNaturalExport.State (C × ParserMemory)) := by
    rw [←archiveParsed]
    exact PSTRSymbolicNaturalExport.state_rebuild _ _ parsed.stk
  have selected : parsed.l=some (.extract 0) := by
    dsimp only [parsed,parserCfg,StoreIso.configuration,LabelMap.configuration]
    rw [pActive]
    rfl
  have shared : extractCfg (⟨some 0,parsed.var,parsed.stk⟩ : PSTRSymbolicNaturalExport.State (C × ParserMemory))=parsed := by
    change (⟨some (.extract 0),parsed.var,parsed.stk⟩ : State C)=parsed
    rw [←selected]
  have ePath := extract_path caller eTrace _ eFinal eFirst eChain eLast' eActive
  let extracted : Segment caller parsed (extractCfg eFinal) (3*(nr.length+dr.length)+9) :=
    ⟨eTrace.map extractCfg,ePath.1.trans (congrArg some (congrArg extractCfg eStart |>.trans shared)),
      ePath.2.1,ePath.2.2,by rw [List.length_map,eLength]⟩
  let whole := front.append extracted
  have parsedContext : parsed.var.1.1=memory.1.1 :=
    congrArg (fun v : C × PSTRSymbolicNaturalExport.Store => v.1) (pFrames pFinal (List.mem_of_getLast? pLast)).1
  have sourceFrame : parsed.stk 15=background 15 := (pFrames pFinal (List.mem_of_getLast? pLast)).2 15 (by decide) (by decide)
  have scratchFrame : parsed.stk 7=background 7 := (pFrames pFinal (List.mem_of_getLast? pLast)).2 7 (by decide) (by decide)
  have contents : (extractCfg eFinal).stk=Function.update parsed.stk 15 (RatInput.Encoder.packet x (background 15)) := by
    change eFinal.stk=_
    rw [←sourceFrame]
    exact PSTRSymbolicNaturalExport.bank_target parsed.stk _
  refine ⟨whole.trace,extractCfg eFinal,parsed,whole.head,whole.chain,whole.last,?_,rfl,parsedContext,contents,
    pTape,scratchFrame,sourceFrame,?_⟩
  · exact List.mem_append_left _ (List.mem_of_getLast? front.last)
  · have count := whole.count
    dsimp only [time,nr,dr] at *
    simp only [List.length_reverse] at count
    omega

end B23_4_RatWordPrep.RawGetter
