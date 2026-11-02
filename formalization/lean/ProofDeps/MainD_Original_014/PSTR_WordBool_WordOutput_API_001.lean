module

public import PSTR_WordBool_WordOutput_Resources_001

/-! Uniform final serializer for original [Rat, Bool-as-Nat, Bool-as-Nat].
The same ONE program reads finite flags and produces every output cell. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordOutput

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def coefficient : Nat := 2048
def degree : Nat := 1
theorem coefficient_pos : 0<coefficient := by decide
theorem degree_pos : 0<degree := by decide
theorem degree_eq_one : degree=1 := rfl

def scale (c d : Nat) (background : Stack → List Bool) (r : Rat) (tail scratch : List Bool) : Nat :=
  RatInput.Encoder.outside background+tail.length+scratch.length+c*(fieldSize r+1)^d

theorem space_le_scale (background : Stack → List Bool) (r : Rat) (tail scratch : List Bool) :
    space background r tail scratch≤scale coefficient degree background r tail scratch := by
  dsimp only [space,scale,coefficient,degree]
  simp only [pow_one]
  omega

theorem entry_stacks (background : Stack → List Bool) (context : C) (hit map : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (r : Rat) (tail scratch : List Bool) :
    let before:=entry background context hit map memory formatter r tail scratch
    before.stk 15=RatInput.Encoder.packet r []++tail ∧ before.stk 7=scratch ∧
      before.stk 3=[] ∧ before.stk 4=[] ∧ before.stk 5=[] ∧ before.stk 6=[] ∧
      before.stk 12=[] ∧ before.stk 13=[] ∧ before.stk 14=[] := by
  refine ⟨?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  change RatInput.Encoder.packet r tail=RatInput.Encoder.packet r []++tail
  simp only [RatInput.Encoder.packet,PSTRSymbolicRatExport.packet,List.cons_append,List.append_assoc,List.nil_append]

structure Facts (source : Label → Statement C) (c d : Nat) (background : Stack → List Bool)
    (context : C) (hit map : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (r : Rat) (tail scratch : List Bool) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry background context hit map memory formatter r tail scratch)
  chain : trace.IsChain (fun a b=>TM2.step source a=some b)
  last : trace.getLast?=some final
  active : final.l=some .done
  context_flags : final.var.1.1=(context,hit,map)
  contents : final.stk=RatInput.Encoder.bank background (RatInput.Encoder.packet r tail) scratch [] [] [] []
    (encode [.rational r,boolDatum hit,boolDatum map]) [] []
  time : trace.length≤scale c d background r tail scratch
  boundaries : ∀ current∈trace,current.var.1.1=(context,hit,map) ∧
    (∀ slot,(current.stk slot).length≤scale c d background r tail scratch) ∧
    RatInput.occupied current.stk≤16*scale c d background r tail scratch ∧
    ∀ slot,¬Work slot→current.stk slot=background slot
  proper : ∀ current∈trace.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        node.1.1.1=(context,hit,map) ∧
        (∀ slot,(node.2 slot).length≤scale c d background r tail scratch+32) ∧
        ∀ slot,¬Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (source point) current.var current.stk≤64*(scale c d background r tail scratch+33)
  syntax_bound : ∀ point,point≠.done→ScannerClock.actions (source point)≤32 ∧ AuxWorkspace.pushes (source point)≤32

theorem actual_word_output (caller : Statement C) (background : Stack → List Bool) (context : C) (hit map : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (r : Rat) (tail scratch : List Bool) :
    ∃ (trace : List (State C)) (final : State C),
      Facts (program caller) coefficient degree background context hit map memory formatter r tail scratch trace final := by
  obtain ⟨trace,final,first,chain,last,active,contextFinal,contentsFinal,count,bounds,proper⟩:=
    actual_output caller background context hit map memory formatter r tail scratch
  have bigger:=space_le_scale background r tail scratch
  have time : trace.length≤scale coefficient degree background r tail scratch := by
    dsimp only [scale,coefficient,degree]
    simp only [pow_one]
    omega
  refine ⟨trace,final,{
    first:=first,chain:=chain,last:=last,active:=active,context_flags:=contextFinal,contents:=contentsFinal,
    time:=time,boundaries:=?_,proper:=?_,syntax_bound:=?_ }⟩
  · intro current member
    have bound:=bounds current member
    exact ⟨bound.1,(fun slot=>(bound.2.1 slot).trans bigger),
      bound.2.2.1.trans (Nat.mul_le_mul_left 16 bigger),bound.2.2.2⟩
  · intro current member
    have currentFacts:=proper current member
    refine ⟨currentFacts.1,?_⟩
    intro point selected
    have internal:=currentFacts.2 point selected
    refine ⟨?_,internal.2.trans (Nat.mul_le_mul_left 64 (Nat.add_le_add_right bigger 33))⟩
    intro node nodeMember
    have nodeFacts:=internal.1 node nodeMember
    exact ⟨nodeFacts.1,(fun slot=>(nodeFacts.2.1 slot).trans (Nat.add_le_add_right bigger 32)),nodeFacts.2.2⟩
  · intro point notDone
    rw [program_proper caller point notDone]
    exact ⟨program_actions point,program_pushes point⟩

theorem final_stacks {source : Label → Statement C} {c d : Nat} {background : Stack → List Bool}
    {context : C} {hit map : Bool} {memory : RatInput.Store} {formatter : WordNatIO.Store}
    {r : Rat} {tail scratch : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source c d background context hit map memory formatter r tail scratch trace final) :
    final.stk 13=encode [.rational r,boolDatum hit,boolDatum map] ∧ final.stk 14=[] ∧
      final.stk 3=[] ∧ final.stk 4=[] ∧ final.stk 5=[] ∧ final.stk 6=[] ∧ final.stk 12=[] ∧
      final.stk 7=scratch ∧ final.stk 15=RatInput.Encoder.packet r tail := by
  rw [facts.contents]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem final_frame {source : Label → Statement C} {c d : Nat} {background : Stack → List Bool}
    {context : C} {hit map : Bool} {memory : RatInput.Store} {formatter : WordNatIO.Store}
    {r : Rat} {tail scratch : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source c d background context hit map memory formatter r tail scratch trace final) :
    ∀ slot,¬Work slot→final.stk slot=background slot := by
  intro slot untouched
  rw [facts.contents]
  exact RatInput.Encoder.bank_frame _ _ _ _ _ _ _ _ _ _ slot untouched

theorem serializer_exists (caller : Statement C) :
    ∃ c d : Nat,∃ source : Label → Statement C,0<c ∧ 0<d ∧ d=1 ∧ source .done=caller ∧
      ∀ (background : Stack → List Bool) (context : C) (hit map : Bool) (memory : RatInput.Store)
        (formatter : WordNatIO.Store) (r : Rat) (tail scratch : List Bool),
        ∃ (trace : List (State C)) (final : State C),
          Facts source c d background context hit map memory formatter r tail scratch trace final := by
  refine ⟨coefficient,degree,program caller,coefficient_pos,degree_pos,degree_eq_one,rfl,?_⟩
  intro background context hit map memory formatter r tail scratch
  exact actual_word_output caller background context hit map memory formatter r tail scratch

end PaperProofs.Common.Native.PSTRWordBool.WordOutput
