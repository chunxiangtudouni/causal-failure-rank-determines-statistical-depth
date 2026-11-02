module

public import RootB234_WordFinalizer_Resources_003
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.WordFinalizer

open Turing
open PaperProofs.Common.Native.PSTRWordBool

variable {C : Type*}

def statementClock (source : Label → Statement C) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (source point) current.var current.stk

def traceClockSum (source : Label → Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock source)).sum

def chargedCost (source : Label → Statement C) (trace : List (State C)) : Nat :=
  trace.length+traceClockSum source trace

theorem statementClock_le {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {old bits : List Bool} {trace : List (State C)} {final current : State C}
    (facts : Facts source frame memory old bits trace final) (member : current∈trace.dropLast) :
    statementClock source current≤28*scale frame old bits := by
  cases selected : current.l with
  | none => simp only [statementClock,selected,Nat.zero_le]
  | some point =>
    simp only [statementClock,selected]
    exact (facts.internal current member point selected).2.2

theorem traceClockSum_le {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {old bits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory old bits trace final) :
    traceClockSum source trace≤112*(scale frame old bits)^2 := by
  have termwise : ∀ clock∈trace.dropLast.map (statementClock source),clock≤28*scale frame old bits := by
    intro clock member
    obtain ⟨current,present,rfl⟩ := List.mem_map.mp member
    exact statementClock_le facts present
  have sumBound : traceClockSum source trace≤trace.dropLast.length*(28*scale frame old bits) := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock source)) (28*scale frame old bits) termwise
  have count : trace.dropLast.length≤4*scale frame old bits := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time
  calc
    traceClockSum source trace≤trace.dropLast.length*(28*scale frame old bits) := sumBound
    _≤(4*scale frame old bits)*(28*scale frame old bits) := Nat.mul_le_mul_right _ count
    _=112*(scale frame old bits)^2 := by ring

theorem chargedCost_le {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {old bits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory old bits trace final) :
    chargedCost source trace≤116*(scale frame old bits)^2 := by
  have power : scale frame old bits≤(scale frame old bits)^2 := by
    simpa only [pow_two,Nat.mul_one] using
      Nat.mul_le_mul_left (scale frame old bits) (Nat.succ_le_of_lt (scale_pos frame old bits))
  have time := facts.time.trans (Nat.mul_le_mul_left 4 power)
  calc
    chargedCost source trace≤4*(scale frame old bits)^2+112*(scale frame old bits)^2 :=
      Nat.add_le_add time (traceClockSum_le facts)
    _=116*(scale frame old bits)^2 := by ring

theorem actual_charged (frame : Stack → List Bool) (memory : Store C) (old bits : List Bool) :
    ∃ trace final,Facts program frame memory old bits trace final ∧
      traceClockSum program trace≤112*(scale frame old bits)^2 ∧
      chargedCost program trace≤116*(scale frame old bits)^2 := by
  obtain ⟨trace,final,facts⟩ := actual_polynomial frame memory old bits
  exact ⟨trace,final,facts,traceClockSum_le facts,chargedCost_le facts⟩

theorem exact_output {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {old bits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory old bits trace final) :
    final.stk 0=bits ∧ final.stk 3=[] ∧ final.stk 13=[] := by
  rw [facts.contents]
  exact ⟨rfl,rfl,rfl⟩

theorem exact_frame {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {old bits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory old bits trace final)
    (slot : Stack) (not0 : slot≠0) (not3 : slot≠3) (not13 : slot≠13) :
    final.stk slot=frame slot := by
  rw [facts.contents]
  exact frame_at _ _ _ _ slot not0 not3 not13

theorem entry_of_state (before : State C) (active : before.l=some .clear) (empty : before.stk 3=[]) :
    entry before.stk before.var (before.stk 0) (before.stk 13)=before := by
  cases before with
  | mk position memory slots =>
    change position=some Label.clear at active
    subst position
    change slots 3=[] at empty
    change (⟨some Label.clear,memory,cells slots (slots 0) [] (slots 13)⟩ : State C)=
      ⟨some Label.clear,memory,slots⟩
    congr 1
    funext slot
    fin_cases slot <;> simp_all [cells]

/-- When consuming an existing configuration, the scale uses only real
input cells. In particular no values on overwritten frame slots can enter
the bound. This also supplies direct linear/quadratic mass-polynomial ABI. -/
theorem scale_le_actual_mass (before : State C) :
    scale before.stk (before.stk 0) (before.stk 13)≤3*(RatInput.occupied before.stk+1) := by
  have old := RatInput.Encoder.point_mass before.stk 0
  have bits := RatInput.Encoder.point_mass before.stk 13
  dsimp only [scale]
  omega

theorem linear_actual_mass (before : State C) (coefficient : Nat) :
    coefficient*scale before.stk (before.stk 0) (before.stk 13)≤
      (3*coefficient)*(RatInput.occupied before.stk+1) := by
  calc
    _≤coefficient*(3*(RatInput.occupied before.stk+1)) :=
      Nat.mul_le_mul_left coefficient (scale_le_actual_mass before)
    _=(3*coefficient)*(RatInput.occupied before.stk+1) := by ring

theorem quadratic_actual_mass (before : State C) (coefficient : Nat) :
    coefficient*(scale before.stk (before.stk 0) (before.stk 13))^2≤
      (9*coefficient)*(RatInput.occupied before.stk+1)^2 := by
  calc
    _≤coefficient*(3*(RatInput.occupied before.stk+1))^2 :=
      Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left (scale_le_actual_mass before) 2)
    _=(9*coefficient)*(RatInput.occupied before.stk+1)^2 := by ring

namespace Public

/-- Explicit finite-store witness. The source never inspects C, and the
actual native consumer fixes a finite C before input. -/
abbrev finiteStore (C : Type*) [Fintype C] : Fintype (Store C) := inferInstance

theorem support_card : support.card=3 := by decide

theorem positive_constants : 0<(4:Nat) ∧ 0<(5:Nat) ∧ 0<(80:Nat) ∧
    0<(6:Nat) ∧ 0<(96:Nat) ∧ 0<(28:Nat) ∧ 0<(112:Nat) ∧ 0<(116:Nat) := by decide

/-- A fixed finite source and support precede all old stacks, true output
bits, caller contexts and frame contents. The same witness carries exact
HALT/output/frame, all boundary/internal resources and total scanner charge. -/
theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (source : Label → Statement C) (labels : Finset Label),
      TM2.Supports source labels ∧ labels.card=3 ∧
      ∀ (frame : Stack → List Bool) (memory : Store C) (old bits : List Bool),
        ∃ trace final,Facts source frame memory old bits trace final ∧
          final.l=none ∧ TM2.step source final=none ∧
          final.stk 0=bits ∧ final.stk 3=[] ∧ final.stk 13=[] ∧
          traceClockSum source trace≤112*(scale frame old bits)^2 ∧
          chargedCost source trace≤116*(scale frame old bits)^2 := by
  refine ⟨program,support,supports,support_card,?_⟩
  intro frame memory old bits
  obtain ⟨trace,final,facts,clock,charged⟩ := actual_charged frame memory old bits
  obtain ⟨out,empty3,empty13⟩ := exact_output facts
  exact ⟨trace,final,facts,facts.halted,facts.halt,out,empty3,empty13,clock,charged⟩

/-- Ordinary default finite control, with no initial-register hypothesis. -/
theorem from_default (frame : Stack → List Bool) (old bits : List Bool) :
    ∃ trace final,Facts (program (C := Unit)) frame default old bits trace final ∧
      final.l=none ∧ final.stk 0=bits ∧ final.stk 3=[] ∧ final.stk 13=[] ∧
      traceClockSum program trace≤112*(scale frame old bits)^2 ∧
      chargedCost program trace≤116*(scale frame old bits)^2 := by
  obtain ⟨trace,final,facts,clock,charged⟩ := actual_charged frame (default : Store Unit) old bits
  obtain ⟨out,empty3,empty13⟩ := exact_output facts
  exact ⟨trace,final,facts,facts.halted,out,empty3,empty13,clock,charged⟩

/-- Direct consumption of an existing real configuration. The only entry
conditions are the active fixed label and empty physical scratch stack 3. -/
theorem from_state (before : State C) (active : before.l=some .clear) (empty : before.stk 3=[]) :
    ∃ trace final,Facts program before.stk before.var (before.stk 0) (before.stk 13) trace final ∧
      trace.head?=some before ∧ final.l=none ∧ final.stk 0=before.stk 13 ∧
      final.stk 3=[] ∧ final.stk 13=[] ∧ final.var.1=before.var.1 ∧
      (∀ slot,slot≠0→slot≠3→slot≠13→final.stk slot=before.stk slot) ∧
      traceClockSum program trace≤112*(scale before.stk (before.stk 0) (before.stk 13))^2 ∧
      chargedCost program trace≤116*(scale before.stk (before.stk 0) (before.stk 13))^2 := by
  obtain ⟨trace,final,facts,clock,charged⟩ := actual_charged before.stk before.var (before.stk 0) (before.stk 13)
  obtain ⟨out,empty3,empty13⟩ := exact_output facts
  exact ⟨trace,final,facts,facts.first.trans (congrArg some (entry_of_state before active empty)),
    facts.halted,out,empty3,empty13,facts.context,exact_frame facts,clock,charged⟩

example : Fintype (Store Unit) := finiteStore Unit
example : (default : Store Unit)=((),false,false) := rfl

end Public
end RootB234.WordFinalizer
