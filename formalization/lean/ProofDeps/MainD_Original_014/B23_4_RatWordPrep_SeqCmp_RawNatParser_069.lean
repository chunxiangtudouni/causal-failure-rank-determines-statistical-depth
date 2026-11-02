module

public import B23_4_RatWordPrep_SeqCmp_OriginalPreludePublic_066

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.RawNat

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMWordFrontCode213

abbrev ParserMemory := BoolOnStacks.Store 19
abbrev ParserState (C : Type*) := VirtualReturn.State C ParserMemory
abbrev ParserStatement (C : Type*) := VirtualReturn.Statement C ParserMemory

def parserSource : Unit → VirtualReturn.SmallStatement ParserMemory := VirtualBool.source alphaMachine

def parserProgram {C : Type*} (caller : ParserStatement C) : Fin 2 → ParserStatement C :=
  VirtualReturn.program parserSource caller

def parserEntry {C : Type*} (context : C) (background : RatInput.Stack → List Bool) : ParserState C :=
  VirtualReturn.configuration context background
    (BoolStackStep.cfg (some ()) 0 false (true::background 1) (background 0))

/-- Literal current physical source0. Only its whole Tape identifies the
raw natural field; the native lift starts from those exact real cells. -/
theorem actual_parser {C : Type*} (context : C) (background : RatInput.Stack → List Bool)
    (number : Nat) (suffix : List Bool)
    (right : ListBlank.mk (background 0)=ListBlank.mk (encodeDatum (.natural number)++suffix++[true])) :
    ∃ (trace : List (ParserState C)) (final : ParserState C),
      trace.head?=some (parserEntry context background) ∧
      trace.IsChain (fun a b => TM2.step (parserProgram .halt) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some 1 ∧
      (VirtualBool.representedState final).Tape=Tape.mk₂
        (false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::true::background 1))
        (suffix++[true]) ∧
      trace.length=(PSTRTMNatValue017.rawPayload number).length^2+9*(PSTRTMNatValue017.rawPayload number).length+5 ∧
      ∀ current∈trace,current.var.1=context ∧ ∀ slot,slot≠0→slot≠1→current.stk slot=background slot := by
  let oldTrace:=alphaTrace (true::background 1) number (suffix++[true])
  let oldFinal:=alphaFinal (true::background 1) number (suffix++[true])
  let oldStart : MachineState 19:=⟨0,Tape.mk₂ (true::background 1) (false::(encodeNat number++(suffix++[true])))⟩
  have oldActual:=alpha_runsFrom (true::background 1) number (suffix++[true])
  obtain ⟨rest,shape⟩:=List.head?_eq_some_iff.mp oldActual.1
  have oldChain : (oldStart::rest).IsChain (fun a b => TM0.step alphaMachine a=some b) := by
    rw [←shape]
    exact oldActual.2.1
  have oldLast : (oldStart::rest).getLast?=some oldFinal := by rw [←shape]; exact oldActual.2.2.1
  let start : BoolOnStacks.State 19:=BoolStackStep.cfg (some ()) 0 false (true::background 1) (background 0)
  have normalized : ListBlank.mk (background 0)=ListBlank.mk (false::(encodeNat number++(suffix++[true]))) := by
    simpa only [encodeDatum,List.cons_append,List.append_assoc] using right
  have representedStart : BoolOnStacks.representedState start=oldStart := by
    change (⟨0,Tape.mk' (ListBlank.mk (true::background 1)) (ListBlank.mk (background 0))⟩ : MachineState 19)=oldStart
    rw [normalized]
    rfl
  obtain ⟨posts,beforeHalt,_length,chain,last,live,represented⟩:=
    BoolStackTrace.lift_path alphaMachine start oldStart oldFinal rest rfl representedStart oldChain oldLast
  have stopped : TM0.step alphaMachine (BoolOnStacks.representedState beforeHalt)=none := by
    rw [represented]
    exact oldActual.2.2.2
  obtain ⟨final,edge,done,unchanged⟩:=BoolStackTrace.terminate alphaMachine beforeHalt live stopped
  let smallTrace:=(start::posts)++[final]
  have smallFirst : smallTrace.head?=some start := rfl
  have smallChain : smallTrace.IsChain (fun a b => TM2.step (BoolOnStacks.program alphaMachine) a=some b) :=
    NativeTrace.join_chain _ _ _ last chain (List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩)
  have smallLast : smallTrace.getLast?=some final := List.getLast?_append_cons _ _ []
  have mapped:=VirtualReturn.path_configuration parserSource .halt context background smallTrace start final smallFirst smallChain smallLast
  have representation : VirtualBool.representedState (VirtualReturn.configuration context background final)=oldFinal :=
    (VirtualBool.represented_configuration context background final).trans (unchanged.trans represented)
  have tape:=congrArg TM0.Cfg.Tape representation
  change (VirtualBool.representedState (VirtualReturn.configuration context background final)).Tape=
    Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::true::background 1))
      (suffix++[true]) at tape
  refine ⟨smallTrace.map (VirtualReturn.configuration context background),VirtualReturn.configuration context background final,
    mapped.1,mapped.2.1,mapped.2.2.1,VirtualReturn.returned context background final done,tape,?_,mapped.2.2.2.2⟩
  rw [List.length_map]
  have oldLength : oldTrace.length=(PSTRTMNatValue017.rawPayload number).length^2+
      9*(PSTRTMNatValue017.rawPayload number).length+4 := by
    simp only [oldTrace,alphaTrace,tagTrace,List.length_append,List.length_map,List.length_cons,List.length_nil,
      PA17TMRatArithmeticParse002.streamTrace_length]
    omega
  have postCount : posts.length=rest.length := _length
  have headCount : oldTrace.length=rest.length+1 := congrArg List.length shape
  have smallCount : smallTrace.length=posts.length+2 := by
    simp only [smallTrace,List.length_append,List.length_cons,List.length_nil]
  omega

theorem finite_archive {C : Type*} (background : RatInput.Stack → List Bool) (number : Nat) (suffix : List Bool)
    (final : ParserState C)
    (tape : (VirtualBool.representedState final).Tape=Tape.mk₂
      (false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::true::background 1))
      (suffix++[true])) :
    ∃ left,final.stk 1=false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::left) := by
  have whole:=congrArg Tape.left tape
  change ListBlank.mk (final.stk 1)=ListBlank.mk
    (false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::true::background 1)) at whole
  let marked:=false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++[false])
  obtain ⟨tail,shape⟩:=PSTRSymbolicNaturalExport.finite_marked_prefix marked (background 1) (final.stk 1)
    (by simpa only [marked,List.cons_append,List.append_assoc,List.nil_append] using whole)
  refine ⟨true::tail,?_⟩
  simpa only [marked,List.cons_append,List.append_assoc,List.nil_append] using shape

end B23_4_RatWordPrep.RawNat
