module

public import Paid.PDROC_BitVM_Native_Lift_002
public import Common.ROOT_ActualTrace_Halting_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.Trace

open Turing PDROC.BitVM.Native

theorem as_full_runs {α : Type*} (next : α → Option α) (start final : α) (run : List α)
    (head : run.head?=some start) (chain : run.IsChain (fun a b=>next a=some b))
    (last : run.getLast?=some final) (halt : next final=none) :
    ROOT.ActualTrace.FullHaltingRuns next start run := by
  refine ⟨head,chain,?_⟩
  intro state stateLast
  rw [last] at stateLast
  have same : final=state := Option.some.inj stateLast
  subst state
  exact halt

theorem final_unique {α : Type*} (next : α → Option α) (start leftEnd rightEnd : α)
    (left right : List α)
    (leftHead : left.head?=some start) (leftChain : left.IsChain (fun a b=>next a=some b))
    (leftLast : left.getLast?=some leftEnd) (leftHalt : next leftEnd=none)
    (rightHead : right.head?=some start) (rightChain : right.IsChain (fun a b=>next a=some b))
    (rightLast : right.getLast?=some rightEnd) (rightHalt : next rightEnd=none) :
    left=right ∧ leftEnd=rightEnd := by
  have same := (as_full_runs next start leftEnd left leftHead leftChain leftLast leftHalt).unique
    (as_full_runs next start rightEnd right rightHead rightChain rightLast rightHalt)
  refine ⟨same,?_⟩
  rw [same,rightLast] at leftLast
  exact (Option.some.inj leftLast).symm

variable {I K Λ σ : Type*} [DecidableEq I] [DecidableEq K]

/-- Every actual lifted complete run projects to the known source run.
This transfers omitted postconditions to the SAME caller-selected path,
without changing the code, choosing a new caller run or assuming one. -/
theorem lifted_run (embedding : I ↪ K) (source : Λ → TM2.Stmt (fun _ : I=>Bool) Λ σ)
    (callerTrace : List (TM2.Cfg (fun _ : K=>Bool) Λ σ))
    (before final : TM2.Cfg (fun _ : K=>Bool) Λ σ)
    (head : callerTrace.head?=some before)
    (chain : callerTrace.IsChain (fun a b=>TM2.step (Lift.machine embedding source) a=some b))
    (last : callerTrace.getLast?=some final) (halt : TM2.step (Lift.machine embedding source) final=none)
    (known : List (TM2.Cfg (fun _ : I=>Bool) Λ σ)) (knownFinal : TM2.Cfg (fun _ : I=>Bool) Λ σ)
    (knownHead : known.head?=some (Lift.cfg embedding before))
    (knownChain : known.IsChain (fun a b=>TM2.step source a=some b))
    (knownLast : known.getLast?=some knownFinal) (knownHalt : TM2.step source knownFinal=none) :
    callerTrace.map (Lift.cfg embedding)=known ∧ Lift.cfg embedding final=knownFinal := by
  have projectedHead : (callerTrace.map (Lift.cfg embedding)).head?=some (Lift.cfg embedding before) := by
    simp only [List.head?_map,head,Option.map_some]
  have projectedChain : (callerTrace.map (Lift.cfg embedding)).IsChain (fun a b=>TM2.step source a=some b) :=
    List.isChain_map_of_isChain _ (fun a b edge=>by
      have actual := Lift.step_project embedding source a
      rw [edge] at actual
      exact actual.symm) chain
  have projectedLast : (callerTrace.map (Lift.cfg embedding)).getLast?=some (Lift.cfg embedding final) := by
    simp only [List.getLast?_map,last,Option.map_some]
  have projectedHalt : TM2.step source (Lift.cfg embedding final)=none := by
    have actual := Lift.step_project embedding source final
    rw [halt] at actual
    exact actual.symm
  exact final_unique (TM2.step source) (Lift.cfg embedding before) (Lift.cfg embedding final) knownFinal
    _ known projectedHead projectedChain projectedLast projectedHalt knownHead knownChain knownLast knownHalt

end PDROC.BitVM.Kernel.Trace
