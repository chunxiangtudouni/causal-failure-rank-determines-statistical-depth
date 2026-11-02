module
public import RootB236_Controller_SelectErase_Semantic005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.SelectErase.Public
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

theorem actual (bg : Stack → List Bool) (memory : Store C) (eligible remaining old5 : List Bool)
    (same : eligible.length=remaining.length) :
    ∃ trace final,Facts bg memory eligible remaining old5 trace final ∧
      traceClockSum trace≤coefficient^2*(inputScale bg eligible remaining old5)^2 ∧
      chargedCost trace≤(coefficient^2+coefficient)*(inputScale bg eligible remaining old5)^2 := by
  obtain ⟨trace,final,facts⟩:=actual_bounded bg memory eligible remaining old5 same
  exact ⟨trace,final,facts,facts.clock_sum,facts.charged⟩

theorem original {q : Nat} (bg : Stack → List Bool) (memory : Store C)
    (eligible remaining : Finset (Fin q)) (old5 : List Bool) :
    ∃ trace final,Facts bg memory (EraseSem.mask eligible) (EraseSem.mask remaining) old5 trace final ∧
      OriginalOutcome bg memory.1 eligible remaining final ∧
      traceClockSum trace≤coefficient^2*(inputScale bg (EraseSem.mask eligible) (EraseSem.mask remaining) old5)^2 ∧
      chargedCost trace≤(coefficient^2+coefficient)*(inputScale bg (EraseSem.mask eligible) (EraseSem.mask remaining) old5)^2 := by
  obtain ⟨trace,final,facts,clock,charge⟩:=actual bg memory (EraseSem.mask eligible) (EraseSem.mask remaining) old5 (by simp)
  exact ⟨trace,final,facts,facts.outcome.original,clock,charge⟩

theorem caller_agrees {bg : Stack → List Bool} {memory : Store C} {eligible remaining old5 : List Bool}
    {trace : List (State C)} {final : State C} (facts : Facts bg memory eligible remaining old5 trace final)
    (found empty : Statement C) (current : State C) (member : current∈trace.dropLast)
    (point : Label) (selected : current.l=some point) : program found empty point=source point := by
  cases point with
  | archive _ | candidate _ | restoreFound _ | restoreEmpty _ | erase _ => rfl
  | found => exact False.elim ((facts.proper current member).1.1 selected)
  | empty => exact False.elim ((facts.proper current member).1.2 selected)

private theorem identity_statement (body : Statement C) : LabelMap.statement id body=body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact congrArg _ ih
  | branch _ _ _ yes no => exact congrArg₂ _ yes no
  | goto _ | halt => rfl
private theorem identity_configuration (current : State C) : LabelMap.configuration id current=current := by
  cases current with
  | mk point memory slots => cases point <;> rfl

theorem caller_chain {bg : Stack → List Bool} {memory : Store C} {eligible remaining old5 : List Bool}
    {trace : List (State C)} {final : State C} (facts : Facts bg memory eligible remaining old5 trace final)
    (found empty : Statement C) : trace.IsChain (fun a b => TM2.step (program found empty) a=some b) := by
  have mapped:=LabelMap.chain_configuration_on id source (program found empty) trace facts.chain
    (by
      intro current member point selected
      rw [identity_statement]
      exact caller_agrees facts found empty current member point selected)
  rw [List.map_id'' identity_configuration trace] at mapped
  exact mapped

def callerClock (found empty : Statement C) (current : State C) : Nat := match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program found empty point) current.var current.stk
def callerClockSum (found empty : Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (callerClock found empty)).sum

theorem caller_clock_sum {bg : Stack → List Bool} {memory : Store C} {eligible remaining old5 : List Bool}
    {trace : List (State C)} {final : State C} (facts : Facts bg memory eligible remaining old5 trace final)
    (found empty : Statement C) : callerClockSum found empty trace=traceClockSum trace := by
  unfold callerClockSum traceClockSum
  congr 1
  apply List.map_congr_left
  intro current member
  cases selected : current.l with
  | none => simp only [callerClock,statementClock,selected]
  | some point => simp only [callerClock,statementClock,selected,caller_agrees facts found empty current member point selected]

theorem noearly {bg : Stack → List Bool} {memory : Store C} {eligible remaining old5 : List Bool}
    {trace : List (State C)} {final : State C} (facts : Facts bg memory eligible remaining old5 trace final) :
    ∀ current∈trace.dropLast,current.l≠some .found ∧ current.l≠some .empty := fun current member => (facts.proper current member).1

/-- All code/support/finite context are fixed before q, masks and old5.
This is one first select/erase operation, not original staging or DFS. -/
theorem fixed_source (C : Type*) [Fintype C] :
    ∃ machine : Label → Statement C,machine=source ∧ TM2.Supports machine support ∧
      machine .found=.halt ∧ machine .empty=.halt ∧
      ∀ bg memory eligible remaining old5,eligible.length=remaining.length→
      ∃ trace final,Facts bg memory eligible remaining old5 trace final ∧
        trace.IsChain (fun a b => TM2.step machine a=some b) := by
  refine ⟨source,rfl,supports .halt .halt,rfl,rfl,?_⟩
  intro bg memory eligible remaining old5 same
  obtain ⟨trace,final,facts⟩:=actual_bounded bg memory eligible remaining old5 same
  exact ⟨trace,final,facts,facts.chain⟩

end RootB236.Controller.SelectErase.Public
