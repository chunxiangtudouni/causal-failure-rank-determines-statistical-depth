module

public import PSTR_WordBool_RatPair_WholeResources_001
public import PSTR_WordBool_RatPair_Serialize_API_002

/-! ALL rational x,y: two existing094 packets to the exact original RCC
two-Rat input. ONE finite Bool source precedes all operand quantifiers. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair

open Turing PSTRWordVM RationalControllerComputation PA17TMRatArithmeticParse002

abbrev Label := Link.Label
abbrev Stack := RatInput.Stack
abbrev Store (C : Type*) := Link.Store C
abbrev Statement (C : Type*) := Link.Statement C
abbrev State (C : Type*) := Link.State C

variable {C : Type*}

def program (caller : Statement C) : Label → Statement C := Link.program caller
def done : Label := Link.done

def packet (p : Rat) (tail : List Bool) : List Bool := RatInput.Encoder.packet p tail

def input (x y : Rat) (tail : List Bool) : List Bool := packet x []++packet y []++tail

def fieldSize (x y : Rat) : Nat :=
  Collector.fieldSize (numeratorDigits x) (denominatorDigits x) (numeratorDigits y) (denominatorDigits y)

def space (background : Stack → List Bool) (x y : Rat) (tail scratch : List Bool) : Nat :=
  Link.space background (numeratorDigits x) (denominatorDigits x) (numeratorDigits y) (denominatorDigits y) tail scratch

def entry (background : Stack → List Bool) (context : C) (oldX oldY : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (x y : Rat) (tail scratch : List Bool) : State C :=
  Link.entry background context oldX oldY memory formatter (sign x) (sign y)
    (numeratorDigits x) (denominatorDigits x) (numeratorDigits y) (denominatorDigits y) tail scratch

theorem packet_append (p : Rat) (tail : List Bool) : packet p tail=packet p []++tail := by
  simp only [packet,RatInput.Encoder.packet,PSTRSymbolicRatExport.packet,List.cons_append,List.append_assoc,List.nil_append]

theorem two_packet_format (x y : Rat) (tail : List Bool) :
    Collector.packets (sign x) (sign y) (numeratorDigits x) (denominatorDigits x)
      (numeratorDigits y) (denominatorDigits y) tail=input x y tail := by
  change packet x (packet y tail)=_
  change packet x (packet y tail)=(packet x []++packet y [])++tail
  have parts:= (packet_append x (packet y tail)).trans
    (congrArg (fun next=>packet x []++next) (packet_append y tail))
  exact parts.trans (List.append_assoc (packet x []) (packet y []) tail).symm

theorem entry_source (background : Stack → List Bool) (context : C) (oldX oldY : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (x y : Rat) (tail scratch : List Bool) :
    (entry background context oldX oldY memory formatter x y tail scratch).stk 15=input x y tail :=
  two_packet_format x y tail

theorem entry_scratch (background : Stack → List Bool) (context : C) (oldX oldY : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (x y : Rat) (tail scratch : List Bool) :
    let before:=entry background context oldX oldY memory formatter x y tail scratch
    before.stk 3=[] ∧ before.stk 4=[] ∧ before.stk 5=[] ∧ before.stk 6=[] ∧
      before.stk 8=[] ∧ before.stk 9=[] ∧ before.stk 12=[] ∧ before.stk 13=[] ∧ before.stk 14=[] ∧
      before.stk 7=scratch := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

structure Facts (source : Label → Statement C) (background : Stack → List Bool) (context : C)
    (oldX oldY : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (x y : Rat) (tail scratch : List Bool) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry background context oldX oldY memory formatter x y tail scratch)
  chain : trace.IsChain (fun a b=>TM2.step source a=some b)
  last : trace.getLast?=some final
  active : final.l=some done
  context_eq : final.var.1.1=(context,sign x,sign y)
  contents : final.stk=Link.finalContents background (input x y tail) scratch (encode [.rational x,.rational y])
  time : trace.length≤8*fieldSize x y+80
  boundaries : ∀ current∈trace,
    (∀ slot,(current.stk slot).length≤space background x y tail scratch) ∧
    RatInput.occupied current.stk≤16*space background x y tail scratch ∧
    ∀ slot,¬Link.Work slot→current.stk slot=background slot
  proper : ∀ current∈trace.dropLast,current.l≠some done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        (∀ slot,(node.2 slot).length≤space background x y tail scratch+32) ∧
        ∀ slot,¬Link.Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (source point) current.var current.stk≤64*(space background x y tail scratch+33)
  syntax_bound : ∀ point,point≠done→ScannerClock.actions (source point)≤32 ∧ AuxWorkspace.pushes (source point)≤32

theorem actual_pair (caller : Statement C) (background : Stack → List Bool) (context : C)
    (oldX oldY : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (x y : Rat) (tail scratch : List Bool) :
    ∃ (trace : List (State C)) (final : State C),
      Facts (program caller) background context oldX oldY memory formatter x y tail scratch trace final := by
  obtain ⟨trace,final,first,chain,last,active,contextFinal,contentsFinal,count,bounds,proper⟩:=
    Link.actual_bounded caller background context oldX oldY memory formatter (sign x) (sign y)
      (numeratorDigits x) (denominatorDigits x) (numeratorDigits y) (denominatorDigits y) tail scratch
  have exactContents : final.stk=Link.finalContents background (input x y tail) scratch
      (encode [.rational x,.rational y]) := by
    rw [two_packet_format,Serializer.output_original2] at contentsFinal
    exact contentsFinal
  refine ⟨trace,final,{
    first:=first,chain:=chain,last:=last,active:=active,context_eq:=contextFinal,
    contents:=exactContents,time:=count,boundaries:=bounds,proper:=proper,syntax_bound:=?_ }⟩
  intro point notDone
  change ScannerClock.actions (Link.program caller point)≤32 ∧ AuxWorkspace.pushes (Link.program caller point)≤32
  rw [Link.program_proper caller point notDone]
  exact ⟨Link.program_actions point,Link.program_pushes point⟩

theorem final_stacks {source : Label → Statement C} {background : Stack → List Bool} {context : C}
    {oldX oldY : Bool} {memory : RatInput.Store} {formatter : WordNatIO.Store}
    {x y : Rat} {tail scratch : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source background context oldX oldY memory formatter x y tail scratch trace final) :
    final.stk 13=encode [.rational x,.rational y] ∧ final.stk 14=[] ∧
      final.stk 7=scratch ∧ final.stk 15=input x y tail ∧
      final.stk 3=[] ∧ final.stk 4=[] ∧ final.stk 5=[] ∧ final.stk 6=[] ∧
      final.stk 8=[] ∧ final.stk 9=[] ∧ final.stk 12=[] := by
  rw [facts.contents]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem final_frame {source : Label → Statement C} {background : Stack → List Bool} {context : C}
    {oldX oldY : Bool} {memory : RatInput.Store} {formatter : WordNatIO.Store}
    {x y : Rat} {tail scratch : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source background context oldX oldY memory formatter x y tail scratch trace final) :
    ∀ slot,¬Link.Work slot→final.stk slot=background slot := by
  intro slot untouched
  rw [facts.contents]
  fin_cases slot <;> first | rfl | exact False.elim (untouched (by decide))

theorem uniform_source (caller : Statement C) :
    ∃ source : Label → Statement C,source done=caller ∧
      ∀ (background : Stack → List Bool) (context : C) (oldX oldY : Bool)
        (memory : RatInput.Store) (formatter : WordNatIO.Store) (x y : Rat) (tail scratch : List Bool),
        ∃ (trace : List (State C)) (final : State C),
          Facts source background context oldX oldY memory formatter x y tail scratch trace final := by
  refine ⟨program caller,rfl,?_⟩
  intro background context oldX oldY memory formatter x y tail scratch
  exact actual_pair caller background context oldX oldY memory formatter x y tail scratch

end PaperProofs.Common.Native.PSTRWordBool.RatPair
