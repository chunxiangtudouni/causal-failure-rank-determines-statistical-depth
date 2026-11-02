module

public import B23_4_RatWordPrep_SeqCmp_RawParser_020

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.RawGetter

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

abbrev Store (C : Type*) := (C × ParserMemory) × PSTRSymbolicNaturalExport.Store

inductive Label where
  | boot
  | parse : Fin 2 → Label
  | extract : PSTRSymbolicNaturalExport.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.boot⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def parserIso (C : Type*) : ((C × PSTRSymbolicNaturalExport.Store) × ParserMemory) ≃ Store C :=
  StoreIso.exchange C PSTRSymbolicNaturalExport.Store ParserMemory

def parserLabel (point : Fin 2) : Label := if point=1 then .extract 0 else .parse point
def extractLabel (point : PSTRSymbolicNaturalExport.Label) : Label := if point=4 then .done else .extract point

def bootMemory (memory : Store C) : Store C := ((memory.1.1,(0,false)),memory.2)

def program (caller : Statement C) : Label → Statement C
  | .boot => .push 1 (fun _ => true) (.load bootMemory (.goto (fun _ => .parse 0)))
  | .parse point => LabelMap.statement parserLabel
      (StoreIso.statement (parserIso C) (parserProgram .halt point))
  | .extract point => LabelMap.statement extractLabel (PSTRSymbolicRatExport.ratProgram point)
  | .done => caller

def parserCfg (before : ParserState (C × PSTRSymbolicNaturalExport.Store)) : State C :=
  LabelMap.configuration parserLabel (StoreIso.configuration (parserIso C) before)
def extractCfg (before : PSTRSymbolicNaturalExport.State (C × ParserMemory)) : State C :=
  LabelMap.configuration extractLabel before

def entry (background : RatInput.Stack → List Bool) (memory : Store C) (x : Rat) (suffix : List Bool) : State C :=
  ⟨some .boot,memory,Function.update background 0 (encodeDatum (.rational x)++suffix)⟩

structure Segment (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget

def Segment.append {caller : Statement C} {before middle final : State C} {A B : Nat}
    (front : Segment caller before middle A) (back : Segment caller middle final B) :
    Segment caller before final (A+B) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.head
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have a := front.count
    have b := back.count
    simp only [List.length_append,List.length_tail]
    omega

theorem boot_step (caller : Statement C) (background : RatInput.Stack → List Bool)
    (memory : Store C) (x : Rat) (suffix : List Bool) :
    TM2.step (program caller) (entry background memory x suffix)=
      some (parserCfg (parserEntry (memory.1.1,memory.2) background x suffix)) := by
  change some (TM2.stepAux (program caller .boot) memory _)=_
  dsimp only [program,TM2.stepAux,entry,bootMemory,parserCfg,parserEntry,
    LabelMap.configuration,StoreIso.configuration,VirtualReturn.configuration,
    VirtualReturn.coreConfiguration,ContextLift.configuration,BoolStackStep.cfg]
  congr 2
  funext slot
  fin_cases slot <;> rfl

theorem parser_path (caller : Statement C) (trace : List (ParserState (C × PSTRSymbolicNaturalExport.Store)))
    (before final : ParserState (C × PSTRSymbolicNaturalExport.Store)) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (parserProgram .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 1) :
    (trace.map parserCfg).head?=some (parserCfg before) ∧
    (trace.map parserCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map parserCfg).getLast?=some (parserCfg final) := by
  let old := parserProgram (C := C × PSTRSymbolicNaturalExport.Store) .halt
  let isoProgram := StoreIso.machine (parserIso C) old
  have iso := StoreIso.actual_path_on (parserIso C) old isoProgram trace before final first chain last
    (by intro current member point selected; rfl)
  have proper := NativeMulLink.no_early_halt_port isoProgram 1 rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped := LabelMap.actual_path_on parserLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      have notOne : point≠1 := by intro same; subst point; exact proper current member selected
      simp only [parserLabel,notOne,ite_false,program]
      rfl)
  have maps : (trace.map (StoreIso.configuration (parserIso C))).map (LabelMap.configuration parserLabel)=
      trace.map parserCfg := by rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem extract_path (caller : Statement C) (trace : List (PSTRSymbolicNaturalExport.State (C × ParserMemory)))
    (before final : PSTRSymbolicNaturalExport.State (C × ParserMemory)) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step PSTRSymbolicRatExport.ratProgram a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 4) :
    (trace.map extractCfg).head?=some (extractCfg before) ∧
    (trace.map extractCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map extractCfg).getLast?=some (extractCfg final) := by
  have proper := NativeMulLink.no_early_halt_port PSTRSymbolicRatExport.ratProgram 4 rfl trace final chain last active
  have mapped := LabelMap.actual_path_on extractLabel PSTRSymbolicRatExport.ratProgram (program caller)
    trace before final first chain last (by
      intro current member point selected
      have notFour : point≠4 := by intro same; subst point; exact proper current member selected
      simp only [extractLabel,notFour,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

end B23_4_RatWordPrep.RawGetter
