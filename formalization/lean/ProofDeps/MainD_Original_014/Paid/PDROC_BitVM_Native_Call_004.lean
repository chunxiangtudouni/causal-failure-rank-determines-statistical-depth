module

public import Paid.PDROC_BitVM_Native_Frame_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.Native

open Turing PaperProofs.Common.Native.PSTRWordBool

variable {K : Type*} [DecidableEq K] {states : ℕ}

/-- A fixed old Bool machine runs on two selected work stacks. Its old
finite control is the only store, and all other stacks hold caller data. -/
def workstackMachine (embed : Fin 2 ↪ K) (old : TM0.Machine Bool (Fin (states+1))) :
    Unit → TM2.Stmt (fun _ : K=>Bool) Unit (BoolOnStacks.Store states) :=
  Lift.machine embed (BoolOnStacks.program old)

/-- Real old arithmetic paths can be reused inside a larger Bool-stack
configuration without assuming an external archive to be empty. Source
trace/cost witnesses are proof data, never inputs to the fixed machine. -/
theorem actual_workstack_trace (embed : Fin 2 ↪ K) (old : TM0.Machine Bool (Fin (states+1)))
    (input : List Bool) (oldTrace : List (TM0.Cfg Bool (Fin (states+1))))
    (oldFinal : TM0.Cfg Bool (Fin (states+1)))
    (before : TM2.Cfg (fun _ : K=>Bool) Unit (BoolOnStacks.Store states))
    (initial : Lift.cfg embed before=TM2.init (Γ:=PushPop.Alphabet) (Λ:=Unit)
      (σ:=BoolOnStacks.Store states) 0 input)
    (head : oldTrace.head?=some (TM0.init input))
    (chain : oldTrace.IsChain (fun a b=>TM0.step old a=some b))
    (last : oldTrace.getLast?=some oldFinal) (halt : TM0.step old oldFinal=none) :
    ∃ (trace : List (TM2.Cfg (fun _ : K=>Bool) Unit (BoolOnStacks.Store states)))
      (final : TM2.Cfg (fun _ : K=>Bool) Unit (BoolOnStacks.Store states)),
      trace.head?=some before ∧
      trace.IsChain (fun a b=>TM2.step (workstackMachine embed old) a=some b) ∧
      trace.getLast?=some final ∧ TM2.step (workstackMachine embed old) final=none ∧
      BoolOnStacks.representedState (Lift.cfg embed final)=oldFinal ∧
      trace.length=oldTrace.length+1 ∧
      ∀ other,(∀ k,other≠embed k)→final.stk other=before.stk other := by
  obtain ⟨source,sourceFinal,sourceHead,sourceChain,sourceLast,sourceHalt,sourceRep,sourceLength⟩ :=
    actual_source_trace old input oldTrace oldFinal head chain last halt
  cases source with
  | nil => simp only [List.head?_nil,reduceCtorEq] at sourceHead
  | cons start rest =>
    have startEq := Option.some.inj sourceHead
    have represented : Lift.cfg embed before=start := initial.trans startEq.symm
    obtain ⟨posts,final,length,liftedChain,liftedLast,finalRep,frame⟩ :=
      Lift.path embed (BoolOnStacks.program old) before start sourceFinal rest represented sourceChain sourceLast
    refine ⟨before::posts,final,rfl,liftedChain,liftedLast,?_,?_,?_,frame⟩
    · apply Lift.halt_project embed (BoolOnStacks.program old) final
      rw [finalRep]
      exact sourceHalt
    · rw [finalRep]
      exact sourceRep
    · simp only [List.length_cons,length] at sourceLength ⊢
      exact sourceLength

omit [DecidableEq K] in
theorem workstack_supports (embed : Fin 2 ↪ K) (old : TM0.Machine Bool (Fin (states+1))) :
    TM2.Supports (workstackMachine embed old) (Finset.univ : Finset Unit) :=
  Lift.supports embed (BoolOnStacks.program old) _ (BoolOnStacks.supports old)

end PDROC.BitVM.Native
