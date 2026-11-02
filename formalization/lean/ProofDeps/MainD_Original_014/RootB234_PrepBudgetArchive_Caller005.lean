module

public import RootB234_PrepBudgetArchive_Public004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepBudgetArchive
open Turing PaperProofs.Common.Native.PSTRWordBool
open scoped BigOperators
variable {C : Type*}

theorem num_proper (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    ∀ current∈(numTrace background context bit flag pending older negative boundary left target).dropLast,
      current.l=some 3 := by
  induction older generalizing bit flag pending target with
  | nil =>
      intro current member
      simp [numTrace] at member
      rcases member with rfl | rfl <;> rfl
  | cons digit rest ih =>
      intro current member
      rw [numTrace,List.dropLast_cons_of_ne_nil (num_nonempty _ _ _ _ _ _ _ _ _ _)] at member
      rcases List.mem_cons.mp member with rfl | rest
      · rfl
      · exact ih _ _ _ _ current rest

theorem den_proper (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    ∀ current∈(denTrace background context bit flag pending later first near older negative boundary left target).dropLast,
      current.l≠some 4 := by
  induction later generalizing bit flag pending target with
  | nil =>
      intro current member
      rw [denTrace,List.dropLast_cons_of_ne_nil (by simp)] at member
      rcases List.mem_cons.mp member with rfl | rest
      · simp [state]
      rw [List.dropLast_cons_of_ne_nil (num_nonempty _ _ _ _ _ _ _ _ _ _)] at rest
      rcases List.mem_cons.mp rest with rfl | tail
      · simp [state]
      · rw [num_proper _ _ _ _ _ _ _ _ _ _ current tail]
        decide
  | cons digit rest ih =>
      intro current member
      rw [denTrace,List.dropLast_cons_of_ne_nil (den_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _)] at member
      rcases List.mem_cons.mp member with rfl | rest
      · simp [state]
      · exact ih _ _ _ _ current rest

theorem actual_proper (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    ∀ current∈(actualTrace background context bit flag pending later first near older negative boundary left target).dropLast,
      current.l≠some 4 := by
  intro current member
  rw [actualTrace,List.dropLast_cons_of_ne_nil (den_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _)] at member
  rcases List.mem_cons.mp member with rfl | rest
  · simp [state]
  · exact den_proper _ _ _ _ _ _ _ _ _ _ _ _ _ current rest

theorem program_caller_agrees (caller : Statement C) (point : Label) (proper : point≠4) :
    program caller point=program .halt point := by
  fin_cases point <;> simp_all [program]

theorem caller_clock (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending : Bool) (later : List Bool) (first near : Bool) (older : List Bool)
    (negative boundary : Bool) (left target : List Bool) (current : State C)
    (member : current∈(actualTrace background context bit flag pending later first near older negative boundary left target).dropLast)
    (point : Label) (selected : current.l=some point) :
    ScannerStatement.clock (program caller point) current.var current.stk=
      statementClock current := by
  have proper : point≠4 := by
    intro same
    subst point
    exact actual_proper _ _ _ _ _ _ _ _ _ _ _ _ _ current member selected
  rw [program_caller_agrees caller point proper]
  simp only [statementClock,selected]

theorem actual_charged (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    (actualTrace background context bit flag pending later first near older negative boundary left target).length+
      traceClockSum (actualTrace background context bit flag pending later first near older negative boundary left target)≤
      13*(scale background later first near older negative boundary left target)^2 := by
  have time := actual_time background context bit flag pending later first near older negative boundary left target
  have clocks := actual_clock_sum background context bit flag pending later first near older negative boundary left target
  have positive : 1≤scale background later first near older negative boundary left target := by simp [scale]
  have square : scale background later first near older negative boundary left target≤
      (scale background later first near older negative boundary left target)^2 := by
    simpa only [pow_two,Nat.mul_one] using
      Nat.mul_le_mul_left (scale background later first near older negative boundary left target) positive
  omega

theorem actual_internal_mass (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool)
    (current : State C)
    (member : current∈actualTrace background context bit flag pending later first near older negative boundary left target)
    (label : Label) (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (inside : node∈AuxWorkspace.nodes (program .halt label) current.var current.stk) :
    (∑ point : Stack,(node.2 point).length)≤16*scale background later first near older negative boundary left target := by
  have each := (trace_internal background context bit flag pending later first near older negative boundary left target
    current member label node inside).2.2.1
  have total := Finset.sum_le_sum (fun (point : Stack) (_ : point∈Finset.univ) => each point)
  simpa using total

end RootB234.PrepBudgetArchive
