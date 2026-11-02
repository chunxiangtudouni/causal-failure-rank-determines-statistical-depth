module

public import B23_4_RatWordPrep_SeqCmp_WordCostPublic_018
public import Common.PSTR_SYM_RatExportResources_095
public import Common.PSTR_WordVM_VirtualBool_025

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

abbrev ParserMemory := BoolOnStacks.Store 45
abbrev ParserState (C : Type*) := VirtualReturn.State C ParserMemory
abbrev ParserStatement (C : Type*) := VirtualReturn.Statement C ParserMemory

def parserSource : Unit → VirtualReturn.SmallStatement ParserMemory := VirtualBool.source ratMachine
def parserProgram {C : Type*} (caller : ParserStatement C) : Fin 2 → ParserStatement C :=
  VirtualReturn.program parserSource caller

def parserEntry {C : Type*} (context : C) (background : RatInput.Stack → List Bool) (x : Rat) (suffix : List Bool) : ParserState C :=
  VirtualReturn.configuration context background
    (BoolStackStep.cfg (some ()) 0 false (true::background 1) (encodeDatum (.rational x)++suffix))

/-- A genuine reusable stream call of the frozen parser. The old path is
constructed here from its proved rational-input theorem, not supplied by
the original caller. The leading TRUE is the caller's paid fresh marker. -/
theorem actual_parser {C : Type*} (context : C) (background : RatInput.Stack → List Bool)
    (x : Rat) (suffix : List Bool) :
    ∃ trace : List (ParserState C), ∃ final : ParserState C,
      trace.head?=some (parserEntry context background x suffix) ∧
      trace.IsChain (fun a b => TM2.step (parserProgram .halt) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some 1 ∧
      (VirtualBool.representedState final).Tape=Tape.mk₂
        (bothLeft (false::sign x::true::background 1) (numeratorDigits x) (denominatorDigits x)) suffix ∧
      trace.length=(numeratorDigits x).length^2+(denominatorDigits x).length^2+
        9*((numeratorDigits x).length+(denominatorDigits x).length)+12 ∧
      ∀ current∈trace,current.var.1=context ∧
        ∀ slot,slot≠0→slot≠1→current.stk slot=background slot := by
  let oldTrace := ratTrace (true::background 1) (sign x) (numeratorDigits x) (denominatorDigits x) suffix
  let oldFinal := ratFinal (true::background 1) (sign x) (numeratorDigits x) (denominatorDigits x) suffix
  let oldStart : TM0.Cfg Bool (Fin 46) := ⟨0,Tape.mk₂ (true::background 1) (encodeDatum (.rational x)++suffix)⟩
  have actual := encodeDatum_rat_runsFrom (true::background 1) suffix x
  obtain ⟨rest,shape⟩ := List.head?_eq_some_iff.mp actual.1
  have oldChain : (oldStart::rest).IsChain (fun a b => TM0.step ratMachine a=some b) := by
    rw [←shape]
    exact actual.2.1
  have oldLast : (oldStart::rest).getLast?=some oldFinal := by rw [←shape]; exact actual.2.2.1
  let start : BoolOnStacks.State 45 := BoolStackStep.cfg (some ()) 0 false (true::background 1) (encodeDatum (.rational x)++suffix)
  obtain ⟨posts,beforeHalt,length,chain,last,live,represented⟩ :=
    BoolStackTrace.lift_path ratMachine start oldStart oldFinal rest rfl rfl oldChain oldLast
  have stopped : TM0.step ratMachine (BoolOnStacks.representedState beforeHalt)=none := by
    rw [represented]
    exact actual.2.2.2
  obtain ⟨final,edge,done,unchanged⟩ := BoolStackTrace.terminate ratMachine beforeHalt live stopped
  let smallTrace := (start::posts)++[final]
  have smallFirst : smallTrace.head?=some start := rfl
  have smallChain : smallTrace.IsChain (fun a b => TM2.step (BoolOnStacks.program ratMachine) a=some b) :=
    NativeTrace.join_chain _ _ _ last chain
      (List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩)
  have smallLast : smallTrace.getLast?=some final := List.getLast?_append_cons _ _ []
  have mapped := VirtualReturn.path_configuration parserSource .halt context background smallTrace start final
    smallFirst smallChain smallLast
  have representation : VirtualBool.representedState (VirtualReturn.configuration context background final)=oldFinal :=
    (VirtualBool.represented_configuration context background final).trans (unchanged.trans represented)
  have tape := congrArg TM0.Cfg.Tape representation
  rw [rat_final_tape] at tape
  refine ⟨smallTrace.map (VirtualReturn.configuration context background),VirtualReturn.configuration context background final,
    mapped.1,mapped.2.1,mapped.2.2.1,VirtualReturn.returned context background final done,tape,?_,mapped.2.2.2.2⟩
  rw [List.length_map]
  have shapeLength := congrArg List.length shape
  have oldLength := ratTrace_length (true::background 1) (sign x) (numeratorDigits x) (denominatorDigits x) suffix
  dsimp only [smallTrace]
  simp only [List.length_append,List.length_cons,List.length_nil]
  simp only [List.length_cons] at shapeLength
  omega

theorem finite_archive {C : Type*} (background : RatInput.Stack → List Bool)
    (x : Rat) (suffix : List Bool) (final : ParserState C)
    (tape : (VirtualBool.representedState final).Tape=Tape.mk₂
      (bothLeft (false::sign x::true::background 1) (numeratorDigits x) (denominatorDigits x)) suffix) :
    ∃ tail,final.stk 1=PSTRSymbolicRatExport.archive (sign x)
      (numeratorDigits x).reverse (denominatorDigits x).reverse (true::tail) := by
  have whole := congrArg Tape.left tape
  let front := false::(PSTRTMRawNat010.leftBlocks (denominatorDigits x).reverse++
    false::(PSTRTMRawNat010.leftBlocks (numeratorDigits x).reverse++false::sign x::[]))
  have marked : ListBlank.mk (final.stk 1)=ListBlank.mk (front++true::background 1) := by
    change ListBlank.mk (final.stk 1)=ListBlank.mk
      (bothLeft (false::sign x::true::background 1) (numeratorDigits x) (denominatorDigits x)) at whole
    simpa only [front,bothLeft,firstLeft,List.cons_append,List.append_assoc,List.nil_append] using whole
  obtain ⟨tail,shape⟩ := PSTRSymbolicNaturalExport.finite_marked_prefix front (background 1) (final.stk 1) marked
  refine ⟨tail,?_⟩
  simpa only [front,PSTRSymbolicRatExport.archive,List.cons_append,List.append_assoc,List.nil_append] using shape

end B23_4_RatWordPrep.RawGetter
