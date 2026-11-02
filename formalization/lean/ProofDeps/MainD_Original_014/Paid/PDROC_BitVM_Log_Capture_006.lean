module

public import Paid.PDROC_BitVM_Log_Capture_005
public import Paid.PDROC_BitVM_Native_Frame_003
public import Paid.PDROC_BitVM_Native_Return_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.Log.Capture

open Turing

/-- The captured reverse word is normalized by the parent-lifted real drain
6→1, including its actual return to3. Input/history/query/result are framed. -/
theorem normalize_run (input archive captured : List Bool) (other : Stack → List Bool) (store : Store) :
    ∃ run : List State,
      run.head? = some (state (some 2) store input [] archive captured other) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some (state (some 3) (none, store.2) input captured.reverse archive [] other) ∧
      run.length = captured.length + 2 := by
  let before : TM2.Cfg (fun _ : Stack => Bool) TwoStack.Label (Option Bool) :=
    ⟨some 0, store.1, slots input [] archive captured other⟩
  let oldOther : TwoStack.Stack → List Bool := fun stack => before.stk (addressEmbed stack)
  let oldStart : TwoStack.State := TwoStack.state 0 1 0 store.1 captured [] oldOther
  let oldFinal : TwoStack.State :=
    ⟨none, none, TwoStack.stackContents 0 1 [] captured.reverse oldOther⟩
  have representation : Native.Lift.cfg addressEmbed before = oldStart := by
    have content : Native.Lift.slots addressEmbed before.stk =
        TwoStack.stackContents 0 1 captured [] oldOther := by
      funext stack
      fin_cases stack <;> simp [Native.Lift.slots, before, oldOther, addressEmbed,
        slots, TwoStack.stackContents]
    exact congrArg (fun contents : TwoStack.Stack → List Bool =>
      (⟨some 0, store.1, contents⟩ : TwoStack.State)) content
  obtain ⟨source, sourceHead, sourceChain, sourceLast, sourceLength⟩ :
      ∃ source : List TwoStack.State,
        source.head? = some oldStart ∧
        source.IsChain (fun a b => TM2.step Query.localDrain a = some b) ∧
        source.getLast? = some oldFinal ∧ source.length = captured.length + 2 := by
    refine ⟨TwoStack.trace 0 1 0 .halt oldOther captured [] store.1,
      TwoStack.trace_head 0 1 0 .halt oldOther captured [] store.1,
      TwoStack.trace_chain Query.localDrain 0 1 (by decide) 0 .halt rfl
        oldOther captured [] store.1, ?_,
      TwoStack.trace_length 0 1 0 .halt oldOther captured [] store.1⟩
    simpa only [List.append_nil, oldFinal, TM2.stepAux] using
      TwoStack.trace_last 0 1 0 .halt oldOther captured [] store.1
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons start rest =>
    have same : start = oldStart := Option.some.inj sourceHead
    subst start
    obtain ⟨posts, liftedFinal, liftedLength, liftedChain, liftedLast, finalRep, frame⟩ :=
      Native.Lift.path addressEmbed Query.localDrain before oldStart oldFinal rest
        representation sourceChain sourceLast
    have liftedHalt : TM2.step (Native.Lift.machine addressEmbed Query.localDrain) liftedFinal = none := by
      apply Native.Lift.halt_project
      rw [finalRep]
      rfl
    have agrees : ∀ label : TwoStack.Label,
        program ((fun _ : TwoStack.Label => (2 : Label)) label) =
          Native.Inline.statement (fun _ : TwoStack.Label => (2 : Label)) 3
            (Native.Lift.machine addressEmbed Query.localDrain label) := by
      intro label
      rfl
    obtain ⟨run, after, head, chain, last, returned, data, localStoreEq, length⟩ :=
      Native.Inline.actual_return_trace (fun _ : TwoStack.Label => (2 : Label)) 3
        (Native.Lift.machine addressEmbed Query.localDrain) program agrees
        (before :: posts) before liftedFinal store.2 rfl liftedChain liftedLast liftedHalt
    have primary : liftedFinal.var = none := by
      have equal := congrArg (fun current : TwoStack.State => current.var) finalRep
      exact equal
    have callerStoreEq : after.var = (none, store.2) := by rw [localStoreEq, primary]
    have contentsEq : after.stk = slots input captured.reverse archive [] other := by
      rw [data]
      funext stack
      fin_cases stack
      · simpa [before, slots] using frame 0 (by intro index; fin_cases index <;> decide)
      · have equal := congrArg (fun current : TwoStack.State => current.stk 1) finalRep
        simpa [Native.Lift.cfg, Native.Lift.slots, addressEmbed, oldFinal,
          TwoStack.stackContents, slots] using equal
      · simpa [before, slots] using frame 2 (by intro index; fin_cases index <;> decide)
      · simpa [before, slots] using frame 3 (by intro index; fin_cases index <;> decide)
      · simpa [before, slots] using frame 4 (by intro index; fin_cases index <;> decide)
      · have equal := congrArg (fun current : TwoStack.State => current.stk 2) finalRep
        simpa [Native.Lift.cfg, Native.Lift.slots, addressEmbed, oldFinal, oldOther,
          before, TwoStack.stackContents, slots] using equal
      · have equal := congrArg (fun current : TwoStack.State => current.stk 0) finalRep
        simpa [Native.Lift.cfg, Native.Lift.slots, addressEmbed, oldFinal,
          TwoStack.stackContents, slots] using equal
    have afterEq : after = state (some 3) (none, store.2) input captured.reverse archive [] other := by
      rcases after with ⟨label, vars, currentSlots⟩
      change label = some 3 at returned
      change vars = (none, store.2) at callerStoreEq
      change currentSlots = slots input captured.reverse archive [] other at contentsEq
      subst label
      subst vars
      subst currentSlots
      rfl
    refine ⟨run, ?_, chain, ?_, ?_⟩
    · exact head
    · simpa only [afterEq] using last
    · simp only [List.length_cons] at length sourceLength
      omega

end PDROC.BitVM.Log.Capture
