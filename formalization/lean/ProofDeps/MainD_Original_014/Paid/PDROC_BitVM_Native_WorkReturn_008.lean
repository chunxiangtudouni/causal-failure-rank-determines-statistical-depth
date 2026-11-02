module

public import Paid.PDROC_BitVM_Native_Return_006
public import Paid.PDROC_BitVM_Native_From_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Native

open Turing PaperProofs.Common.Native.PSTRWordBool

variable {K Ω τ : Type*} [DecidableEq K] {states : ℕ}

def returnedState (embed : Fin 2 ↪ K)
    (state : TM2.Cfg (fun _ : K=>Bool) Ω (BoolOnStacks.Store states×τ)) :
    TM0.Cfg Bool (Fin (states+1)) :=
  BoolOnStacks.representedState (Lift.cfg embed
    (⟨none,state.var.1,state.stk⟩ : TM2.Cfg (fun _ : K=>Bool) Unit (BoolOnStacks.Store states)))

/-- Genuine arbitrary-tape arithmetic call inside a caller: fixed work
stacks, real return label, unchanged other stacks and exact old cost+1.
Initialization of the work tape and subsequent result parsing are separate
real caller operations, not conclusions of this component. -/
theorem actual_workstack_return (embed : Fin 2 ↪ K)
    (old : TM0.Machine Bool (Fin (states+1))) (callLabel returnLabel : Ω)
    (caller : Ω → TM2.Stmt (fun _ : K=>Bool) Ω (BoolOnStacks.Store states×τ))
    (agrees : caller callLabel=Inline.statement (fun _ : Unit=>callLabel) returnLabel
      (workstackMachine embed old ()))
    (before : TM2.Cfg (fun _ : K=>Bool) Unit (BoolOnStacks.Store states)) (extra : τ)
    (oldTrace : List (TM0.Cfg Bool (Fin (states+1))))
    (oldStart oldFinal : TM0.Cfg Bool (Fin (states+1)))
    (active : (Lift.cfg embed before).l=some ())
    (representation : BoolOnStacks.representedState (Lift.cfg embed before)=oldStart)
    (head : oldTrace.head?=some oldStart)
    (chain : oldTrace.IsChain (fun a b=>TM0.step old a=some b))
    (last : oldTrace.getLast?=some oldFinal) (halt : TM0.step old oldFinal=none) :
    ∃ (trace : List (TM2.Cfg (fun _ : K=>Bool) Ω (BoolOnStacks.Store states×τ)))
      (final : TM2.Cfg (fun _ : K=>Bool) Ω (BoolOnStacks.Store states×τ)),
      trace.head?=some (Inline.cfg (fun _ : Unit=>callLabel) returnLabel extra before) ∧
      trace.IsChain (fun a b=>TM2.step caller a=some b) ∧ trace.getLast?=some final ∧
      final.l=some returnLabel ∧ returnedState embed final=oldFinal ∧
      final.var.2=extra ∧ trace.length=oldTrace.length+1 ∧
      ∀ other,(∀ k,other≠embed k)→final.stk other=before.stk other := by
  obtain ⟨source,sourceFinal,sourceHead,sourceChain,sourceLast,sourceHalt,sourceRep,sourceLength,frame⟩ :=
    actual_workstack_traceFrom embed old before oldTrace oldStart oldFinal
      active representation head chain last halt
  have agreesAll : ∀ label : Unit,caller ((fun _ : Unit=>callLabel) label)=
      Inline.statement (fun _ : Unit=>callLabel) returnLabel (workstackMachine embed old label) := by
    intro label
    cases label
    exact agrees
  obtain ⟨trace,final,first,actual,lastActual,returned,stackData,store,length⟩ :=
    Inline.actual_return_trace (fun _ : Unit=>callLabel) returnLabel
      (workstackMachine embed old) caller agreesAll source before sourceFinal extra
      sourceHead sourceChain sourceLast sourceHalt
  refine ⟨trace,final,first,actual,lastActual,returned,?_,?_,length.trans sourceLength,?_⟩
  · unfold returnedState
    rw [stackData,store]
    exact sourceRep
  · rw [store]
  · intro other outside
    rw [stackData]
    exact frame other outside

end PDROC.BitVM.Native
