module

public import Paid.PDROC_BitVM_Native_Call_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Native

open Turing PaperProofs.Common.Native.PSTRWordBool

variable {states : ℕ}

/-- Reuse an old machine's genuine run from an arbitrary physical tape,
including real left archives and suffixes. No init/reset or padding is
inferred from the source run. The local final halt remains an actual step. -/
theorem actual_source_traceFrom (old : TM0.Machine Bool (Fin (states+1)))
    (before : BoolOnStacks.State states)
    (oldTrace : List (TM0.Cfg Bool (Fin (states+1))))
    (oldStart oldFinal : TM0.Cfg Bool (Fin (states+1)))
    (active : before.l=some ()) (representation : BoolOnStacks.representedState before=oldStart)
    (head : oldTrace.head?=some oldStart)
    (chain : oldTrace.IsChain (fun a b=>TM0.step old a=some b))
    (last : oldTrace.getLast?=some oldFinal) (halt : TM0.step old oldFinal=none) :
    ∃ (trace : List (BoolOnStacks.State states)) (final : BoolOnStacks.State states),
      trace.head?=some before ∧ trace.IsChain (fun a b=>TM2.step (BoolOnStacks.program old) a=some b) ∧
      trace.getLast?=some final ∧ TM2.step (BoolOnStacks.program old) final=none ∧
      BoolOnStacks.representedState final=oldFinal ∧ trace.length=oldTrace.length+1 := by
  cases oldTrace with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have same : start=oldStart := Option.some.inj head
    subst start
    obtain ⟨posts,beforeHalt,length,sourceChain,sourceLast,live,represented⟩ :=
      lift_path old before oldStart oldFinal rest active representation chain last
    have actualHalt : TM0.step old (BoolOnStacks.representedState beforeHalt)=none := by
      rw [represented]
      exact halt
    obtain ⟨final,haltEdge,done,unchanged⟩ := terminate old beforeHalt live actualHalt
    have lastPair : (beforeHalt::[final]).IsChain
        (fun a b=>TM2.step (BoolOnStacks.program old) a=some b) :=
      List.isChain_cons_cons.mpr ⟨haltEdge,List.isChain_singleton _⟩
    refine ⟨(before::posts)++[final],final,rfl,
      NativeTrace.join_chain _ _ _ sourceLast sourceChain lastPair,?_,
      source_halted old final done,unchanged.trans represented,?_⟩
    · exact List.getLast?_append_cons (before::posts) final []
    · simp only [List.length_append,List.length_cons,List.length_nil,length]

variable {K : Type*} [DecidableEq K]

/-- Arbitrary-tape old arithmetic runs on selected real work stacks, while
all other caller stacks are framed through the entire actual execution. -/
theorem actual_workstack_traceFrom (embed : Fin 2 ↪ K) (old : TM0.Machine Bool (Fin (states+1)))
    (before : TM2.Cfg (fun _ : K=>Bool) Unit (BoolOnStacks.Store states))
    (oldTrace : List (TM0.Cfg Bool (Fin (states+1))))
    (oldStart oldFinal : TM0.Cfg Bool (Fin (states+1)))
    (active : (Lift.cfg embed before).l=some ())
    (representation : BoolOnStacks.representedState (Lift.cfg embed before)=oldStart)
    (head : oldTrace.head?=some oldStart)
    (chain : oldTrace.IsChain (fun a b=>TM0.step old a=some b))
    (last : oldTrace.getLast?=some oldFinal) (halt : TM0.step old oldFinal=none) :
    ∃ (trace : List (TM2.Cfg (fun _ : K=>Bool) Unit (BoolOnStacks.Store states)))
      (final : TM2.Cfg (fun _ : K=>Bool) Unit (BoolOnStacks.Store states)),
      trace.head?=some before ∧ trace.IsChain (fun a b=>TM2.step (workstackMachine embed old) a=some b) ∧
      trace.getLast?=some final ∧ TM2.step (workstackMachine embed old) final=none ∧
      BoolOnStacks.representedState (Lift.cfg embed final)=oldFinal ∧
      trace.length=oldTrace.length+1 ∧
      ∀ other,(∀ k,other≠embed k)→final.stk other=before.stk other := by
  obtain ⟨source,sourceFinal,sourceHead,sourceChain,sourceLast,sourceHalt,sourceRep,sourceLength⟩ :=
    actual_source_traceFrom old (Lift.cfg embed before) oldTrace oldStart oldFinal
      active representation head chain last halt
  cases source with
  | nil => simp only [List.head?_nil,reduceCtorEq] at sourceHead
  | cons start rest =>
    have represented : Lift.cfg embed before=start := (Option.some.inj sourceHead).symm
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

end PDROC.BitVM.Native
