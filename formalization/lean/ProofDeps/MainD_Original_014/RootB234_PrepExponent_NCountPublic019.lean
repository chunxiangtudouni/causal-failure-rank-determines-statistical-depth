module

public import RootB234_PrepExponent_NCountResources018

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NCount
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

theorem caller_agrees (caller : Statement C) (point : Label) (different : point≠.done) :
    program caller point=program .halt point := by
  cases point with
  | copy _ | reverse _ | unary _ | move _ | clear _ => rfl
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


theorem caller_chain (caller : Statement C) {background : Stack → List Bool} {context : C}
    {registers : Unary.Registers} {rat : RatInput.Store} {flags : RatOutput.Store} {number : Nat}
    {memory : PacketUnary.Store C} {run : List (State C)}
    (facts : Facts background context registers rat flags number memory run) :
    run.IsChain (fun a b => TM2.step (program caller) a=some b) := by
  apply chain_same _ _ _ facts.chain
  intro current member point selected
  apply caller_agrees caller point
  intro same
  subst point
  exact (facts.proper current member).1 selected

def callerClock (caller : Statement C) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program caller point) current.var current.stk

def callerClockSum (caller : Statement C) (run : List (State C)) : Nat :=
  (run.dropLast.map (callerClock caller)).sum

theorem caller_clock_sum (caller : Statement C) {background : Stack → List Bool} {context : C}
    {registers : Unary.Registers} {rat : RatInput.Store} {flags : RatOutput.Store} {number : Nat}
    {memory : PacketUnary.Store C} {run : List (State C)}
    (facts : Facts background context registers rat flags number memory run) :
    callerClockSum caller run=traceClockSum run := by
  unfold callerClockSum traceClockSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro current member
  cases selected : current.l with
  | none => simp only [callerClock,statementClock,selected]
  | some point =>
    have different : point≠.done := by intro same;subst point;exact (facts.proper current member).1 selected
    simp only [callerClock,statementClock,selected,caller_agrees caller point different]

theorem final_mass (background : Stack → List Bool) (number : Nat) :
    RatInput.occupied (bank background (B23_4_RatWordPrep.NatField.packet number []) [] [] (Unary.unary number) []) ≤
      16*(initialMass background number+number) := by
  let before := bank background (B23_4_RatWordPrep.NatField.packet number []) [] [] [] []
  have equal : bank background (B23_4_RatWordPrep.NatField.packet number []) [] [] (Unary.unary number) []=
      Function.update before 11 (Unary.unary number) := by
    funext slot
    fin_cases slot <;> rfl
  rw [equal]
  apply RatInput.Encoder.occupied_bound
  intro slot
  by_cases same : slot=11
  · subst slot
    simp only [Function.update_self,Unary.unary,List.length_replicate]
    omega
  · have bound := RatInput.Encoder.point_mass before slot
    rw [Function.update_of_ne same]
    exact bound.trans (Nat.le_add_right _ _)

namespace Public

theorem actual (caller : Statement C) (background : Stack → List Bool) (context : C)
    (registers : Unary.Registers) (rat : RatInput.Store) (flags : RatOutput.Store) (number : Nat) :
    ∃ memory run,Facts background context registers rat flags number memory run ∧
      run.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      callerClockSum caller run ≤ 68719476736*(scale background number)^4 ∧
      run.length+callerClockSum caller run ≤ 68719493120*(scale background number)^4 := by
  obtain ⟨memory,run,facts⟩ := actual_bounded background context registers rat flags number
  exact ⟨memory,run,facts,caller_chain caller facts,
    (caller_clock_sum caller facts).symm ▸ traceClockSum_le facts,
    (caller_clock_sum caller facts).symm ▸ chargedCost_le facts⟩

theorem fixed_source (C : Type*) [Finite C] :
    ∃ (source : Label → Statement C) (allowed : Finset Label),
      source=program .halt ∧ TM2.Supports source allowed ∧ Finite (Store C) ∧
      ∀ (background : Stack → List Bool) (context : C) (registers : Unary.Registers)
        (rat : RatInput.Store) (flags : RatOutput.Store) (number : Nat),
        ∃ memory run,Facts background context registers rat flags number memory run ∧
          traceClockSum run ≤ 68719476736*(scale background number)^4 ∧
          run.length+traceClockSum run ≤ 68719493120*(scale background number)^4 := by
  refine ⟨program .halt,Finset.univ,rfl,supports .halt,inferInstance,?_⟩
  intro background context registers rat flags number
  obtain ⟨memory,run,facts⟩ := actual_bounded background context registers rat flags number
  exact ⟨memory,run,facts,traceClockSum_le facts,chargedCost_le facts⟩

theorem from_state (before : State C) (number : Nat) (active : before.l=some (.copy .boot))
    (packet : before.stk 8=B23_4_RatWordPrep.NatField.packet number [])
    (e3 : before.stk 3=[]) (e5 : before.stk 5=[]) (e6 : before.stk 6=[])
    (e11 : before.stk 11=[]) (e15 : before.stk 15=[]) :
    ∃ memory run,Facts before.stk before.var.1.1.1 before.var.1.1.2 before.var.1.2 before.var.2 number memory run ∧
      run.head?=some before ∧ run.IsChain (fun a b => TM2.step (program .halt) a=some b) := by
  have bankSame : bank before.stk (B23_4_RatWordPrep.NatField.packet number []) [] [] [] []=before.stk := by
    funext slot
    fin_cases slot <;> simp [bank,packet,e3,e5,e6,e11,e15]
  have stateSame : state before.stk (.copy .boot) before.var
      (B23_4_RatWordPrep.NatField.packet number []) [] [] [] []=before := by
    cases before with
    | mk position memory contents =>
      change position=some (.copy .boot) at active
      subst position
      unfold state
      rw [bankSame]
  obtain ⟨memory,run,facts⟩ := actual_bounded before.stk before.var.1.1.1 before.var.1.1.2
    before.var.1.2 before.var.2 number
  exact ⟨memory,run,facts,facts.first.trans (congrArg some stateSame),facts.chain⟩

end Public
end RootB234.PrepExponent.NCount
