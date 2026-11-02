module
public import Mathlib.Data.List.Chain

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace ROOT.ActualTrace
universe u
variable {α : Type u}

/-- A designated first exit need not halt the transition function. -/
structure FirstExit (next : α → Option α) (terminal : α → Prop) (start : α) (trace : List α) : Prop where
  head : trace.head?=some start
  chain : trace.IsChain (fun before after=>next before=some after)
  last : ∀ state,trace.getLast?=some state→terminal state
  proper : ∀ state∈trace.dropLast,¬terminal state

/-- Determinism identifies complete FIRST-exit lists. The designated
terminal may have an executable successor outside this callee trace. -/
theorem firstExit_trace_unique (next : α → Option α) (terminal : α → Prop) :
    ∀ left right : List α,left≠[]→right≠[]→left.head?=right.head?→
      left.IsChain (fun before after=>next before=some after)→
      right.IsChain (fun before after=>next before=some after)→
      (∀ state,left.getLast?=some state→terminal state)→
      (∀ state,right.getLast?=some state→terminal state)→
      (∀ state∈left.dropLast,¬terminal state)→
      (∀ state∈right.dropLast,¬terminal state)→left=right := by
  intro left
  induction left with
  | nil => intro right nonempty;exact False.elim (nonempty rfl)
  | cons a tail ih =>
    intro right _ rightNonempty heads leftChain rightChain leftLast rightLast leftProper rightProper
    cases right with
    | nil => exact False.elim (rightNonempty rfl)
    | cons b rest =>
      have same : a=b:=Option.some.inj heads
      subst b
      cases tail with
      | nil =>
        cases rest with
        | nil => rfl
        | cons c cs =>
          exact False.elim ((rightProper a (by rw [List.dropLast_cons_cons];exact List.mem_cons.mpr (Or.inl rfl))) (leftLast a rfl))
      | cons c cs =>
        cases rest with
        | nil =>
          exact False.elim ((leftProper a (by rw [List.dropLast_cons_cons];exact List.mem_cons.mpr (Or.inl rfl))) (rightLast a rfl))
        | cons d ds =>
          have leftEdge:=List.isChain_cons_cons.mp leftChain
          have rightEdge:=List.isChain_cons_cons.mp rightChain
          have sameNext : c=d:=Option.some.inj (leftEdge.1.symm.trans rightEdge.1)
          subst d
          have tails : c::cs=c::ds:=ih (c::ds) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) rfl leftEdge.2 rightEdge.2
            (by simpa only [List.getLast?_cons_cons] using leftLast)
            (by simpa only [List.getLast?_cons_cons] using rightLast)
            (fun state member=>leftProper state (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem a member))
            (fun state member=>rightProper state (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem a member))
          exact congrArg (List.cons a) tails

theorem FirstExit.unique {next : α → Option α} {terminal : α → Prop} {start : α} {left right : List α}
    (first : FirstExit next terminal start left) (second : FirstExit next terminal start right) : left=right := by
  have leftNonempty : left≠[]:=by intro empty;simpa only [empty,List.head?_nil,reduceCtorEq] using first.head
  have rightNonempty : right≠[]:=by intro empty;simpa only [empty,List.head?_nil,reduceCtorEq] using second.head
  exact firstExit_trace_unique next terminal left right leftNonempty rightNonempty (first.head.trans second.head.symm)
    first.chain second.chain first.last second.last first.proper second.proper

/-- API matching ordinary head/last witnesses of two callee theorems. -/
theorem firstExit_unique_of_endpoints (next : α → Option α) (terminal : α → Prop)
    (start leftEnd rightEnd : α) (left right : List α)
    (leftHead : left.head?=some start) (rightHead : right.head?=some start)
    (leftChain : left.IsChain (fun before after=>next before=some after))
    (rightChain : right.IsChain (fun before after=>next before=some after))
    (leftLast : left.getLast?=some leftEnd) (rightLast : right.getLast?=some rightEnd)
    (leftTerminal : terminal leftEnd) (rightTerminal : terminal rightEnd)
    (leftProper : ∀ state∈left.dropLast,¬terminal state) (rightProper : ∀ state∈right.dropLast,¬terminal state) :
    left=right ∧ leftEnd=rightEnd := by
  have first : FirstExit next terminal start left:=⟨leftHead,leftChain,fun state ending=>by
    have same : leftEnd=state:=Option.some.inj (leftLast.symm.trans ending)
    exact same ▸ leftTerminal,leftProper⟩
  have second : FirstExit next terminal start right:=⟨rightHead,rightChain,fun state ending=>by
    have same : rightEnd=state:=Option.some.inj (rightLast.symm.trans ending)
    exact same ▸ rightTerminal,rightProper⟩
  have same:=first.unique second
  exact ⟨same,Option.some.inj (leftLast.symm.trans ((congrArg List.getLast? same).trans rightLast))⟩

end ROOT.ActualTrace
