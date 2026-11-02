module

public import RootB234_PrepExponent_NatToRatResources007

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NatToRat
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
variable {C : Type*}

theorem caller_agrees (caller : Statement C) (point : Label) (different : point≠.done) :
    program caller point=program .halt point := by
  cases point with
  | prepare | copy _ | reverse _ | header => rfl
  | done => exact False.elim (different rfl)

private theorem chain_same (old target : Label → Statement C) (trace : List (State C))
    (chain : trace.IsChain (fun a b => TM2.step old a=some b))
    (same : ∀ before∈trace.dropLast,∀ point,before.l=some point→target point=old point) :
    trace.IsChain (fun a b => TM2.step target a=some b) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons first rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      apply List.isChain_cons_cons.mpr
      refine ⟨?_,ih tailChain ?_⟩
      · cases first with
        | mk position memory slots =>
          cases position with
          | none => cases edge
          | some point =>
            have equality:=same ⟨some point,memory,slots⟩
              (by rw [List.dropLast_cons_cons]; exact List.mem_cons_self) point rfl
            change some (TM2.stepAux (target point) memory slots)=some next
            rw [equality]
            exact edge
      · intro current present point active
        apply same current _ point active
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ present

theorem caller_chain (caller : Statement C) {background : Stack → List Bool} {memory : Store C}
    {number : Nat} {tail : List Bool} {run : List (State C)} (facts : Facts background memory number tail run) :
    run.IsChain (fun a b => TM2.step (program caller) a=some b) := by
  apply chain_same _ _ _ facts.chain
  intro current member point selected
  apply caller_agrees caller point
  intro equal
  subst point
  exact (facts.proper current member).1 selected

theorem caller_internal (caller : Statement C) {background : Stack → List Bool} {memory : Store C}
    {number : Nat} {tail : List Bool} {run : List (State C)} (facts : Facts background memory number tail run) :
    ∀ current∈run.dropLast,∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (program caller point) current.var current.stk,
        node.1.1=memory.1 ∧ (∀ slot,(node.2 slot).length ≤ 57*scale background number tail) ∧
        ∀ slot,¬Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (program caller point) current.var current.stk ≤ 464*scale background number tail := by
  intro current member point selected
  have different : point≠.done := by
    intro equal
    subst point
    exact (facts.proper current member).1 selected
  rw [caller_agrees caller point different]
  exact (facts.proper current member).2 point selected

def callerClock (caller : Statement C) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program caller point) current.var current.stk

def callerClockSum (caller : Statement C) (run : List (State C)) : Nat :=
  (run.dropLast.map (callerClock caller)).sum

theorem caller_clock_sum (caller : Statement C) {background : Stack → List Bool} {memory : Store C}
    {number : Nat} {tail : List Bool} {run : List (State C)} (facts : Facts background memory number tail run) :
    callerClockSum caller run=traceClockSum run := by
  unfold callerClockSum traceClockSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro current member
  cases selected : current.l with
  | none => simp only [callerClock,statementClock,selected]
  | some point =>
    have different : point≠.done := by
      intro equal
      subst point
      exact (facts.proper current member).1 selected
    simp only [callerClock,statementClock,selected,caller_agrees caller point different]

namespace Public

theorem actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (number : Nat) (tail : List Bool) :
    ∃ run,Facts background memory number tail run ∧
      run.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      callerClockSum caller run ≤ 6032*(scale background number tail)^2 ∧
      run.length+callerClockSum caller run ≤ 6045*(scale background number tail)^2 := by
  obtain ⟨run,facts⟩ := actual_bounded background memory number tail
  exact ⟨run,facts,caller_chain caller facts,
    (caller_clock_sum caller facts).symm ▸ traceClockSum_le facts,
    (caller_clock_sum caller facts).symm ▸ chargedCost_le facts⟩

theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (source : Label → Statement C) (allowed : Finset Label),
      source=program .halt ∧ TM2.Supports source allowed ∧ Finite (Store C) ∧
      ∀ (background : Stack → List Bool) (memory : Store C) (number : Nat) (tail : List Bool),
        ∃ run,Facts background memory number tail run ∧
          traceClockSum run ≤ 6032*(scale background number tail)^2 ∧
          run.length+traceClockSum run ≤ 6045*(scale background number tail)^2 := by
  refine ⟨program .halt,Finset.univ,rfl,supports .halt,inferInstance,?_⟩
  intro background memory number tail
  obtain ⟨run,facts⟩ := actual_bounded background memory number tail
  exact ⟨run,facts,traceClockSum_le facts,chargedCost_le facts⟩

end Public
end RootB234.PrepExponent.NatToRat
