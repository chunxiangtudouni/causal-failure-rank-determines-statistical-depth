module

public import PSTR_WordBool_RatCmp_Resources_001

/-! Uniform ALL signed rational LE callee. Fixed source/positive scale
precede ALL operands. The caller supplies only the original two-Rat input. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatCmp

open Turing PSTRWordVM RationalControllerComputation

abbrev Label := Link.Label
abbrev Stack := RatOutput.Stack
abbrev states : Nat := Link.states
abbrev Store (C : Type*) := Link.Store C
abbrev Statement (C : Type*) := Link.Statement C
abbrev State (C : Type*) := Link.State C

variable {C : Type*}

def program (caller : Statement C) : Label → Statement C := Link.program caller
def done : Label := Link.done
def coefficient : Nat := Link.coefficient
def degree : Nat := Link.degree

theorem coefficient_pos : 0<coefficient := Link.coefficient_pos
theorem degree_pos : 0<degree := Link.degree_pos
theorem degree_eq_four : degree=4 := rfl

def scale (c d : Nat) (background : Stack → List Bool) (x y : Rat) : Nat :=
  1024*(IsolatedRat.outside background+1)+c*((encode [.rational x,.rational y]).length+1)^d

def entry (context : C) (flags : Reader.Store) (readerMemory : RatOutput.Store)
    (nativeMemory : BoolOnStacks.Store states) (background : Stack → List Bool) (x y : Rat) : State C :=
  Link.entry context flags readerMemory nativeMemory background x y

theorem entry_stacks (context : C) (flags : Reader.Store) (readerMemory : RatOutput.Store)
    (nativeMemory : BoolOnStacks.Store states) (background : Stack → List Bool) (x y : Rat) :
    let before:=entry context flags readerMemory nativeMemory background x y
    before.stk 13=encode [.rational x,.rational y] ∧ before.stk 14=[] ∧
      ∀ slot,slot≠13→slot≠14→before.stk slot=background slot := by
  refine ⟨rfl,rfl,?_⟩
  intro slot not13 not14
  change IsolatedRat.cells background (encode [.rational x,.rational y]) [] slot=background slot
  simp only [IsolatedRat.cells,not13,not14,ite_false]

structure Facts (source : Label → Statement C) (c d : Nat) (context : C) (flags : Reader.Store)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : Stack → List Bool) (x y : Rat) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry context flags readerMemory nativeMemory background x y)
  chain : trace.IsChain (fun a b=>TM2.step source a=some b)
  last : trace.getLast?=some final
  active : final.l=some done
  context_eq : final.var.1.1.1=context
  right : final.stk 13=[]
  left : final.stk 14=[]
  counter : final.stk 7=background 7
  restored : final.stk 15=background 15
  result : final.stk 3=decide (x≤y)::background 3
  frame : ∀ slot,slot≠3→slot≠13→slot≠14→slot≠15→final.stk slot=background slot
  time : trace.length≤scale c d background x y
  boundaries : ∀ current∈trace,current.var.1.1.1=context ∧
    (∀ slot,(current.stk slot).length≤scale c d background x y) ∧
    RatOutput.occupied current.stk≤16*scale c d background x y ∧
    ∀ slot,¬Link.Work slot→current.stk slot=background slot
  proper : ∀ current∈trace.dropLast,current.l≠some done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        (∀ slot,(node.2 slot).length≤scale c d background x y+3) ∧
        ∀ slot,¬Link.Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (source point) current.var current.stk≤16*(scale c d background x y+4)
  syntax_bound : ∀ point,point≠done→ScannerClock.actions (source point)≤8 ∧ AuxWorkspace.pushes (source point)≤3

theorem actual_le (caller : Statement C) (context : C) (flags : Reader.Store)
    (readerMemory : RatOutput.Store) (nativeMemory : BoolOnStacks.Store states)
    (background : Stack → List Bool) (x y : Rat) :
    ∃ (trace : List (State C)) (final : State C),
      Facts (program caller) coefficient degree context flags readerMemory nativeMemory background x y trace final := by
  obtain ⟨trace,final,first,chain,last,active,contextFinal,right,left,counter,restored,result,frame,count,bounds,proper⟩:=
    Link.actual_bounded caller context flags readerMemory nativeMemory background x y
  refine ⟨trace,final,{
    first:=first,chain:=chain,last:=last,active:=active,context_eq:=contextFinal,right:=right,left:=left,
    counter:=counter,restored:=restored,result:=result,frame:=frame,time:=?_,boundaries:=?_,proper:=?_,syntax_bound:=?_ }⟩
  · simpa only [scale,coefficient,degree,Link.budget] using count
  · simpa only [scale,coefficient,degree,Link.budget] using bounds
  · simpa only [scale,coefficient,degree,Link.budget,program,done] using proper
  · intro point notDone
    change ScannerClock.actions (Link.program caller point)≤8 ∧ AuxWorkspace.pushes (Link.program caller point)≤3
    rw [Link.program_proper caller point notDone]
    exact ⟨Link.program_actions point,Link.program_pushes point⟩

theorem comparison_callee_exists (caller : Statement C) :
    ∃ c d : Nat,∃ source : Label → Statement C,0<c ∧ 0<d ∧ d=4 ∧ source done=caller ∧
      ∀ (context : C) (flags : Reader.Store) (readerMemory : RatOutput.Store)
        (nativeMemory : BoolOnStacks.Store states) (background : Stack → List Bool) (x y : Rat),
        ∃ (trace : List (State C)) (final : State C),
          Facts source c d context flags readerMemory nativeMemory background x y trace final := by
  refine ⟨coefficient,degree,program caller,coefficient_pos,degree_pos,degree_eq_four,rfl,?_⟩
  intro context flags readerMemory nativeMemory background x y
  exact actual_le caller context flags readerMemory nativeMemory background x y

end PaperProofs.Common.Native.PSTRWordBool.RatCmp
