module

public import RootB234_RuntimeCounter_Round_Resources_006
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.RuntimeCounter.Round

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRTMIncrement009

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
    {memory : Store C} {digits : List Bool} {trace : List (State C)} {final current : State C}
    (facts : Facts source frame memory digits trace final) (member : current∈trace.dropLast) :
    statementClock source current≤4128*scale frame digits := by
  cases selected : current.l with
  | none => simp only [statementClock,selected,Nat.zero_le]
  | some point =>
    simp only [statementClock,selected]
    exact (facts.internal current member point selected).2

theorem traceClockSum_le {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {digits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory digits trace final) :
    traceClockSum source trace≤1056768*(scale frame digits)^2 := by
  have termwise : ∀ clock∈trace.dropLast.map (statementClock source),clock≤4128*scale frame digits := by
    intro clock member
    obtain ⟨current,present,rfl⟩ := List.mem_map.mp member
    exact statementClock_le facts present
  have sumBound : traceClockSum source trace≤trace.dropLast.length*(4128*scale frame digits) := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock source)) (4128*scale frame digits) termwise
  have count : trace.dropLast.length≤256*scale frame digits := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time
  calc
    traceClockSum source trace≤trace.dropLast.length*(4128*scale frame digits) := sumBound
    _≤(256*scale frame digits)*(4128*scale frame digits) := Nat.mul_le_mul_right _ count
    _=1056768*(scale frame digits)^2 := by ring

theorem chargedCost_le {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {digits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory digits trace final) :
    chargedCost source trace≤1057024*(scale frame digits)^2 := by
  have power : scale frame digits≤(scale frame digits)^2 := by
    simpa only [pow_two,Nat.mul_one] using
      Nat.mul_le_mul_left (scale frame digits) (Nat.succ_le_of_lt (scale_pos frame digits))
  have time := facts.time.trans (Nat.mul_le_mul_left 256 power)
  calc
    chargedCost source trace≤256*(scale frame digits)^2+1056768*(scale frame digits)^2 :=
      Nat.add_le_add time (traceClockSum_le facts)
    _=1057024*(scale frame digits)^2 := by ring

theorem actual_charged (frame : Stack → List Bool) (memory : Store C) (digits : List Bool) :
    ∃ trace final,Facts program frame memory digits trace final ∧
      traceClockSum program trace≤1056768*(scale frame digits)^2 ∧
      chargedCost program trace≤1057024*(scale frame digits)^2 := by
  obtain ⟨trace,final,facts⟩ := actual_polynomial frame memory digits
  exact ⟨trace,final,facts,traceClockSum_le facts,chargedCost_le facts⟩

theorem exact_output {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {digits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory digits trace final) :
    final.stk 10=Raw.packet (Raw.outputDigits digits) ∧ final.stk 11=[false] ∧ final.stk 4=[] := by
  rw [facts.contents]
  exact ⟨rfl,rfl,rfl⟩

theorem exact_frame {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {digits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory digits trace final) (slot : Stack) (untouched : ¬Work slot) :
    final.stk slot=frame slot := by
  rw [facts.contents]
  exact cells_frame _ _ _ _ slot untouched

theorem finite_flags {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {digits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory digits trace final) :
    initialZero final.var.2=decide (valueDigits digits=0) ∧
      afterZero final.var.2=decide (valueDigits digits≤1) := by
  constructor
  · unfold initialZero
    rw [facts.decoded]
    rfl
  · unfold afterZero
    rw [facts.decoded]
    rfl

theorem entry_of_state (before : State C) (digits : List Bool)
    (active : before.l=some 0) (right : before.stk 10=Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[]) :
    entry before.stk before.var digits=before := by
  cases before with
  | mk position memory slots =>
    change position=some 0 at active
    subst position
    change slots 10=Raw.packet digits at right
    change slots 11=[false] at left
    change slots 4=[] at scratch
    change (⟨some 0,memory,cells slots (Raw.packet digits) [false] []⟩ : State C)=
      ⟨some 0,memory,slots⟩
    congr 1
    funext slot
    fin_cases slot <;> simp_all [cells]

namespace Public

abbrev entryLabel : Label := 0
abbrev zeroLabel : Label := 7
abbrev positiveLabel : Label := 8

abbrev finiteStore (C : Type*) [Fintype C] : Fintype (Store C) := inferInstance

theorem positive_coefficients : 0<(256:Nat) ∧ 0<(513:Nat) ∧ 0<(8208:Nat) ∧
    0<(515:Nat) ∧ 0<(8240:Nat) ∧ 0<(4128:Nat) ∧ 0<(1056768:Nat) ∧ 0<(1057024:Nat) := by decide

/-- Source, control and support are fixed before every finite digit word,
including all-zero/padded words. The initial store is arbitrary and is
initialized by one actual load. Neither a host width nor positivity is input. -/
theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (source : Label → Statement C) (labels : Finset Label),
      TM2.Supports source labels ∧ source zeroLabel=.halt ∧ source positiveLabel=.halt ∧
      ∀ (frame : Stack → List Bool) (memory : Store C) (digits : List Bool),
        ∃ trace final,Facts source frame memory digits trace final ∧
          final.stk 10=Raw.packet (Raw.outputDigits digits) ∧ final.stk 11=[false] ∧ final.stk 4=[] ∧
          (Raw.outputDigits digits).length=digits.length ∧
          valueDigits (Raw.outputDigits digits)=valueDigits digits-1 ∧
          initialZero final.var.2=decide (valueDigits digits=0) ∧
          afterZero final.var.2=decide (valueDigits digits≤1) ∧
          traceClockSum source trace≤1056768*(scale frame digits)^2 ∧
          chargedCost source trace≤1057024*(scale frame digits)^2 := by
  refine ⟨program,support,supports,rfl,rfl,?_⟩
  intro frame memory digits
  obtain ⟨trace,final,facts,clock,charged⟩ := actual_charged frame memory digits
  obtain ⟨right,left,scratch⟩ := exact_output facts
  obtain ⟨initialFlag,nextFlag⟩ := finite_flags facts
  exact ⟨trace,final,facts,right,left,scratch,output_width digits,output_value digits,
    initialFlag,nextFlag,clock,charged⟩

theorem ports {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {digits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory digits trace final) :
    (final.l=some zeroLabel ↔ valueDigits digits=0) ∧
      (final.l=some positiveLabel ↔ 0<valueDigits digits) := by
  by_cases zero : valueDigits digits=0
  · rw [facts.port]
    simp [zero,zeroLabel,positiveLabel]
  · rw [facts.port]
    simp [zero,zeroLabel,positiveLabel,Nat.pos_of_ne_zero zero]

/-- N=1 still takes the POSITIVE round port; new-zero is its independent
finite flag. A subsequent invocation will take the initial-zero port. -/
theorem one_round_new_zero {source : Label → Statement C} {frame : Stack → List Bool}
    {memory : Store C} {digits : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts source frame memory digits trace final) (one : valueDigits digits=1) :
    final.l=some positiveLabel ∧ afterZero final.var.2=true ∧ valueDigits (Raw.outputDigits digits)=0 := by
  have flags := finite_flags facts
  have value := output_value digits
  refine ⟨?_,?_,?_⟩
  · rw [facts.port]
    simp [one]
  · simpa [one] using flags.2
  · simpa only [one,Nat.sub_self] using value

theorem twice_value (count : Nat) :
    valueDigits (false::PSTRTMNatValue017.rawPayload count)=2*count := by
  simp [valueDigits,Nat.bit,PSTRTMNatValue017.valueDigits_rawPayload]

theorem from_twice (frame : Stack → List Bool) (memory : Store C) (count : Nat) :
    ∃ trace final,Facts program frame memory (false::PSTRTMNatValue017.rawPayload count) trace final ∧
      valueDigits (Raw.outputDigits (false::PSTRTMNatValue017.rawPayload count))=2*count-1 ∧
      traceClockSum program trace≤1056768*(scale frame (false::PSTRTMNatValue017.rawPayload count))^2 ∧
      chargedCost program trace≤1057024*(scale frame (false::PSTRTMNatValue017.rawPayload count))^2 := by
  obtain ⟨trace,final,facts,clock,charged⟩ := actual_charged frame memory (false::PSTRTMNatValue017.rawPayload count)
  refine ⟨trace,final,facts,?_,clock,charged⟩
  simpa only [twice_value] using output_value (false::PSTRTMNatValue017.rawPayload count)

theorem from_default (frame : Stack → List Bool) (digits : List Bool) :
    ∃ trace final,Facts (program (C := Unit)) frame default digits trace final ∧
      traceClockSum program trace≤1056768*(scale frame digits)^2 ∧
      chargedCost program trace≤1057024*(scale frame digits)^2 := actual_charged frame default digits

/-- A direct actual-entry endpoint. S is proved equal to the real entry
occupied mass plus one; there is no supplied space/path/fuel/width premise. -/
theorem from_state (before : State C) (digits : List Bool)
    (active : before.l=some entryLabel) (right : before.stk 10=Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[]) :
    ∃ (trace : List (State C)) (final : State C),Facts (program (C := C)) before.stk before.var digits trace final ∧
      trace.head?=some before ∧ scale before.stk digits=occupied before.stk+1 ∧
      traceClockSum (program (C := C)) trace≤1056768*(occupied before.stk+1)^2 ∧
      chargedCost (program (C := C)) trace≤1057024*(occupied before.stk+1)^2 := by
  cases before with
  | mk point memory slots =>
    change point=some 0 at active
    subst point
    change slots 10=Raw.packet digits at right
    change slots 11=[false] at left
    change slots 4=[] at scratch
    have same : cells slots (Raw.packet digits) [false] []=slots := by
      funext slot
      fin_cases slot <;> simp_all [cells]
    obtain ⟨trace,final,facts,clock,charged⟩ := actual_charged (C := C) slots memory digits
    have first := facts.first
    change trace.head?=some (⟨some 0,memory,cells slots (Raw.packet digits) [false] []⟩ : State C) at first
    rw [same] at first
    have mass : scale slots digits=occupied slots+1 := by
      change occupied (cells slots (Raw.packet digits) [false] [])+1=occupied slots+1
      rw [same]
    refine ⟨trace,final,facts,first,mass,?_,?_⟩
    · exact clock.trans (le_of_eq (congrArg (fun size : Nat => 1056768*size^2) mass))
    · exact charged.trans (le_of_eq (congrArg (fun size : Nat => 1057024*size^2) mass))

end Public
end RootB234.RuntimeCounter.Round
