module
public import RootB236_Controller_ResumeErase_Semantic005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.ResumeErase.Public
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

theorem actual (bg : Stack → List Bool) (memory : Store C) (bits parent old4 old5 : List Bool) (k : Nat)
    (extent : k+bits.length=parent.length) :
    ∃ trace final,Facts bg memory bits parent old4 old5 k trace final ∧
      traceClockSum trace≤coefficient^2*(inputScale bg bits parent old4 old5 k)^2 ∧
      chargedCost trace≤(coefficient^2+coefficient)*(inputScale bg bits parent old4 old5 k)^2 := by
  obtain ⟨trace,final,facts⟩:=actual_bounded bg memory bits parent old4 old5 k extent
  exact ⟨trace,final,facts,facts.clock_sum,facts.charged⟩

/-- The saved tools are a suffix of the SAME parent's original finRange
candidate list. This qualification is caller-frame state, not raw input
or a new filter against arbitrary old child remaining4. -/
theorem original_tail {q : Nat} (bg : Stack → List Bool) (memory : Store C)
    (eligible parent : Finset (Fin q)) (tools : List (Fin q)) (bits old4 old5 : List Bool) (k : Nat)
    (extent : k+bits.length=q) (suffix : ParentSuffix eligible parent tools)
    (represented : ControllerCandidate.pending k bits=tools.map Fin.val) :
    ∃ trace final,Facts bg memory bits (EraseSem.mask parent) old4 old5 k trace final ∧
      OriginalOutcome bg memory.1 eligible parent tools final ∧
      traceClockSum trace≤coefficient^2*(inputScale bg bits (EraseSem.mask parent) old4 old5 k)^2 ∧
      chargedCost trace≤(coefficient^2+coefficient)*(inputScale bg bits (EraseSem.mask parent) old4 old5 k)^2 := by
  obtain ⟨trace,final,facts,clock,charge⟩:=actual bg memory bits (EraseSem.mask parent) old4 old5 k (by simpa using extent)
  exact ⟨trace,final,facts,facts.outcome.original suffix represented,clock,charge⟩

theorem caller_agrees {bg : Stack → List Bool} {memory : Store C} {bits parent old4 old5 : List Bool} {k : Nat}
    {trace : List (State C)} {final : State C} (facts : Facts bg memory bits parent old4 old5 k trace final)
    (found empty : Statement C) (current : State C) (member : current∈trace.dropLast)
    (point : Label) (selected : current.l=some point) : program found empty point=source point := by
  cases point with
  | clear => rfl
  | body point =>
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

theorem caller_chain {bg : Stack → List Bool} {memory : Store C} {bits parent old4 old5 : List Bool} {k : Nat}
    {trace : List (State C)} {final : State C} (facts : Facts bg memory bits parent old4 old5 k trace final)
    (found empty : Statement C) : trace.IsChain (fun a b => TM2.step (program found empty) a=some b) := by
  have mapped:=LabelMap.chain_configuration_on id source (program found empty) trace facts.chain
    (by intro current member point selected;rw [identity_statement];exact caller_agrees facts found empty current member point selected)
  rw [List.map_id'' identity_configuration trace] at mapped
  exact mapped

def callerClock (found empty : Statement C) (current : State C) : Nat := match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program found empty point) current.var current.stk
def callerClockSum (found empty : Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (callerClock found empty)).sum
theorem caller_clock_sum {bg : Stack → List Bool} {memory : Store C} {bits parent old4 old5 : List Bool} {k : Nat}
    {trace : List (State C)} {final : State C} (facts : Facts bg memory bits parent old4 old5 k trace final)
    (found empty : Statement C) : callerClockSum found empty trace=traceClockSum trace := by
  unfold callerClockSum traceClockSum
  congr 1
  apply List.map_congr_left
  intro current member
  cases selected : current.l with
  | none => simp only [callerClock,statementClock,selected]
  | some point => simp only [callerClock,statementClock,selected,caller_agrees facts found empty current member point selected]

theorem noearly {bg : Stack → List Bool} {memory : Store C} {bits parent old4 old5 : List Bool} {k : Nat}
    {trace : List (State C)} {final : State C} (facts : Facts bg memory bits parent old4 old5 k trace final) :
    ∀ current∈trace.dropLast,current.l≠some foundPort ∧ current.l≠some emptyPort := fun current member => (facts.proper current member).1

theorem fixed_source (C : Type*) [Fintype C] :
    ∃ machine : Label → Statement C,machine=source ∧ TM2.Supports machine support ∧
      machine foundPort=.halt ∧ machine emptyPort=.halt ∧
      ∀ bg memory bits parent old4 old5 k,k+bits.length=parent.length→
      ∃ trace final,Facts bg memory bits parent old4 old5 k trace final ∧
        trace.IsChain (fun a b => TM2.step machine a=some b) := by
  refine ⟨source,rfl,supports .halt .halt,rfl,rfl,?_⟩
  intro bg memory bits parent old4 old5 k extent
  obtain ⟨trace,final,facts⟩:=actual_bounded bg memory bits parent old4 old5 k extent
  exact ⟨trace,final,facts,facts.chain⟩
end RootB236.Controller.ResumeErase.Public
