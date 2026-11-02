module

public import RootB236_Controller_Erase_Resources003
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.Erase

open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

def scale (background : Stack → List Bool) (skipped suffix : List Bool) : Nat :=
  backgroundMass background+(2*skipped.length+suffix.length+1)+3

structure Facts (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix : List Bool)
    (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (state background (some 0) (context,present,saved)
    (skipped++head::suffix) (List.replicate skipped.length true) [])
  chain : trace.IsChain (fun before after => TM2.step program before=some after)
  last : trace.getLast?=some final
  contents : final=state background none (context,false,false)
    (skipped++false::suffix) (List.replicate skipped.length true) []
  halted : final.l=none
  halt : TM2.step program final=none
  time : trace.length=2*skipped.length+3
  boundary : ∀ current∈trace,
    WorkBound background context (2*skipped.length+suffix.length+1) current

theorem actual_facts (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix : List Bool) :
    Facts background context present saved skipped head suffix
      (actualTrace background context present saved skipped head suffix [])
      (state background none (context,false,false) (skipped++false::suffix)
        (List.replicate skipped.length true) []) := by
  refine ⟨actual_head _ _ _ _ _ _ _ _,actual_chain _ _ _ _ _ _ _ _,?_,rfl,rfl,rfl,?_,?_⟩
  · simpa using actual_last background context present saved skipped head suffix []
  · simpa using actual_length background context present saved skipped head suffix []
  · simpa using actual_bound background context present saved skipped head suffix []

theorem scale_pos (background : Stack → List Bool) (skipped suffix : List Bool) :
    0<scale background skipped suffix := by
  dsimp [scale]
  omega

theorem Facts.time_le {background : Stack → List Bool} {context : C} {present saved : Bool}
    {skipped : List Bool} {head : Bool} {suffix : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts background context present saved skipped head suffix trace final) :
    trace.length ≤ 2*scale background skipped suffix := by
  rw [facts.time]
  dsimp [scale]
  omega

theorem Facts.context {background : Stack → List Bool} {context : C} {present saved : Bool}
    {skipped : List Bool} {head : Bool} {suffix : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts background context present saved skipped head suffix trace final)
    (current : State C) (member : current∈trace) : current.var.1=context :=
  work_context _ _ _ _ (facts.boundary current member)

theorem Facts.frame {background : Stack → List Bool} {context : C} {present saved : Bool}
    {skipped : List Bool} {head : Bool} {suffix : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts background context present saved skipped head suffix trace final)
    (current : State C) (member : current∈trace) (point : Stack)
    (notMask : point≠4) (notCount : point≠5) (notParked : point≠7) :
    current.stk point=background point :=
  work_frame _ _ _ _ (facts.boundary current member) point notMask notCount notParked

theorem Facts.internal {background : Stack → List Bool} {context : C} {present saved : Bool}
    {skipped : List Bool} {head : Bool} {suffix : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts background context present saved skipped head suffix trace final)
    (current : State C) (member : current∈trace) (label : Label)
    (node : AuxWorkspace.Snapshot (Γ := Alphabet) (σ := Store C))
    (inside : node∈AuxWorkspace.nodes (program label) current.var current.stk) :
    node.1.1=context ∧
      (∀ point,¬Work point→node.2 point=background point) ∧
      (∀ point,(node.2 point).length≤scale background skipped suffix) ∧
      (AuxWorkspace.nodes (program label) current.var current.stk).length≤5 ∧
      ScannerStatement.clock (program label) current.var current.stk≤6*scale background skipped suffix := by
  refine ⟨(nodes_context label current.var current.stk node inside).trans (facts.context current member),
    ?_,?_,program_nodes label current.var current.stk,work_clock_bound _ _ _ _ (facts.boundary current member) label⟩
  · intro point untouched
    rw [nodes_frame label current.var current.stk point untouched node inside]
    have outside : point≠4 ∧ point≠5 ∧ point≠7 := by simpa only [Work,not_or] using untouched
    exact facts.frame current member point outside.1 outside.2.1 outside.2.2
  · intro point
    have bound:=work_internal_bound background context _ current (facts.boundary current member) label node inside point
    dsimp [scale]
    omega

def statementClock (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program point) current.var current.stk

def traceClockSum (trace : List (State C)) : Nat := (trace.dropLast.map statementClock).sum

theorem Facts.clock_sum {background : Stack → List Bool} {context : C} {present saved : Bool}
    {skipped : List Bool} {head : Bool} {suffix : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts background context present saved skipped head suffix trace final) :
    traceClockSum trace≤12*(scale background skipped suffix)^2 := by
  have terms : ∀ clock∈trace.dropLast.map statementClock,clock≤6*scale background skipped suffix := by
    intro clock member
    obtain ⟨current,withinTrace,rfl⟩:=List.mem_map.mp member
    have within:=facts.boundary current (List.dropLast_subset trace withinTrace)
    cases selected : current.l with
    | none => simp [statementClock,selected]
    | some point =>
        simp only [statementClock,selected]
        exact work_clock_bound _ _ _ _ within point
  have sumBound : traceClockSum trace≤trace.dropLast.length*(6*scale background skipped suffix) := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map statementClock) (6*scale background skipped suffix) terms
  have count : trace.dropLast.length≤2*scale background skipped suffix := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time_le
  calc
    traceClockSum trace≤trace.dropLast.length*(6*scale background skipped suffix) := sumBound
    _≤(2*scale background skipped suffix)*(6*scale background skipped suffix) := Nat.mul_le_mul_right _ count
    _=12*(scale background skipped suffix)^2 := by ring

theorem Facts.charged {background : Stack → List Bool} {context : C} {present saved : Bool}
    {skipped : List Bool} {head : Bool} {suffix : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts background context present saved skipped head suffix trace final) :
    trace.length+traceClockSum trace≤14*(scale background skipped suffix)^2 := by
  have power : scale background skipped suffix≤(scale background skipped suffix)^2 := by
    simpa only [pow_two,Nat.mul_one] using
      Nat.mul_le_mul_left (scale background skipped suffix) (Nat.succ_le_of_lt (scale_pos background skipped suffix))
  calc
    trace.length+traceClockSum trace≤2*(scale background skipped suffix)^2+12*(scale background skipped suffix)^2 :=
      Nat.add_le_add (facts.time_le.trans (Nat.mul_le_mul_left 2 power)) facts.clock_sum
    _=14*(scale background skipped suffix)^2 := by ring

namespace Public

theorem actual (background : Stack → List Bool) (context : C) (present saved : Bool)
    (skipped : List Bool) (head : Bool) (suffix : List Bool) :
    ∃ trace final,Facts background context present saved skipped head suffix trace final ∧
      traceClockSum trace≤12*(scale background skipped suffix)^2 ∧
      trace.length+traceClockSum trace≤14*(scale background skipped suffix)^2 := by
  have facts:=actual_facts background context present saved skipped head suffix
  exact ⟨_,_,facts,facts.clock_sum,facts.charged⟩

theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (source : Label → Statement C) (support : Finset Label),
      source=program ∧ support.card=2 ∧ TM2.Supports source support ∧
      ∀ (background : Stack → List Bool) (context : C) (present saved : Bool)
        (skipped : List Bool) (head : Bool) (suffix : List Bool),
        ∃ trace final,Facts background context present saved skipped head suffix trace final ∧
          traceClockSum trace≤12*(scale background skipped suffix)^2 ∧
          trace.length+traceClockSum trace≤14*(scale background skipped suffix)^2 := by
  exact ⟨program,Finset.univ,rfl,by decide,supports,actual⟩

end Public
end RootB236.Controller.Erase
