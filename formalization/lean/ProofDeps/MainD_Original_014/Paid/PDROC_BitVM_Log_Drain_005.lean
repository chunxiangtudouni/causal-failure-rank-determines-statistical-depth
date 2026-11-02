module

public import Paid.PDROC_BitVM_Log_Query_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

/-! The two actual drains needed by the lookup caller: valueReverse6→5 and
historyArchive2→0. This is a concrete data macro over the fixed seven stacks,
using the existing source drain and parent lifting/return theorems. -/

namespace PDROC.BitVM.Log.Drain

open Turing

abbrev Stack := Query.Stack
abbrev Label := Fin 3
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Query.Store
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def source (valueMode : Bool) : Stack := if valueMode then 6 else 2
def target (valueMode : Bool) : Stack := if valueMode then 5 else 0

def embed (valueMode : Bool) : TwoStack.Stack ↪ Stack where
  toFun := fun index => if index = 0 then source valueMode else if index = 1 then target valueMode else 4
  inj' := by
    intro left right equal
    cases valueMode <;> fin_cases left <;> fin_cases right <;> simp_all [source, target]

def code (valueMode : Bool) : Statement :=
  Native.Inline.statement (τ := Query.Extra) (fun _ : TwoStack.Label => (0 : Label)) 1
    (Native.Lift.statement (embed valueMode) (Query.localDrain 0))

def program (valueMode : Bool) (label : Label) : Statement :=
  if label = 0 then code valueMode else .halt

def slots (valueMode : Bool) (word rest : List Bool) (other : Stack → List Bool) : Stack → List Bool :=
  fun index => if index = source valueMode then word else if index = target valueMode then rest else other index

def state (valueMode : Bool) (label : Option Label) (store : Store) (word rest : List Bool)
    (other : Stack → List Bool) : State := ⟨label, store, slots valueMode word rest other⟩

theorem supports (valueMode : Bool) : TM2.Supports (program valueMode) (Finset.univ : Finset Label) := by
  have closed : TM2.SupportsStmt (Finset.univ : Finset Label) (code valueMode) := by
    apply Native.Inline.supports_statement
      (fun _ : TwoStack.Label => (0 : Label)) 1 (Finset.univ : Finset TwoStack.Label)
      (Finset.univ : Finset Label)
    · intro label _; exact Finset.mem_univ _
    · exact Finset.mem_univ _
    · apply Native.Lift.supports_statement
      simp [Query.localDrain, TwoStack.drain, TM2.SupportsStmt]
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    · simpa [program] using closed
    · simp [program, TM2.SupportsStmt]
    · simp [program, TM2.SupportsStmt]

/-- Real return boundary, with exact other-stack and finite-flag carry. -/
theorem return_run (valueMode : Bool) (word rest : List Bool) (other : Stack → List Bool) (store : Store) :
    ∃ run : List State,
      run.head? = some (state valueMode (some 0) store word rest other) ∧
      run.IsChain (fun a b => TM2.step (program valueMode) a = some b) ∧
      run.getLast? = some (state valueMode (some 1) (none, store.2) [] (word.reverse ++ rest) other) ∧
      run.length = word.length + 2 := by
  let before : TM2.Cfg (fun _ : Stack => Bool) TwoStack.Label (Option Bool) :=
    ⟨some 0, store.1, slots valueMode word rest other⟩
  let oldOther : TwoStack.Stack → List Bool := fun index => before.stk (embed valueMode index)
  let oldStart : TwoStack.State := TwoStack.state 0 1 0 store.1 word rest oldOther
  let oldFinal : TwoStack.State :=
    ⟨none, none, TwoStack.stackContents 0 1 [] (word.reverse ++ rest) oldOther⟩
  have representation : Native.Lift.cfg (embed valueMode) before = oldStart := by
    have content : Native.Lift.slots (embed valueMode) before.stk =
        TwoStack.stackContents 0 1 word rest oldOther := by
      funext index
      cases valueMode <;> fin_cases index <;>
        simp [Native.Lift.slots, before, oldOther, embed, slots, source, target, TwoStack.stackContents]
    exact congrArg (fun contents : TwoStack.Stack → List Bool =>
      (⟨some 0, store.1, contents⟩ : TwoStack.State)) content
  obtain ⟨path, pathHead, pathChain, pathLast, pathLength⟩ :
      ∃ path : List TwoStack.State,
        path.head? = some oldStart ∧
        path.IsChain (fun a b => TM2.step Query.localDrain a = some b) ∧
        path.getLast? = some oldFinal ∧ path.length = word.length + 2 := by
    exact ⟨TwoStack.trace 0 1 0 .halt oldOther word rest store.1,
      TwoStack.trace_head 0 1 0 .halt oldOther word rest store.1,
      TwoStack.trace_chain Query.localDrain 0 1 (by decide) 0 .halt rfl oldOther word rest store.1,
      TwoStack.trace_last 0 1 0 .halt oldOther word rest store.1,
      TwoStack.trace_length 0 1 0 .halt oldOther word rest store.1⟩
  cases path with
  | nil => simp only [List.head?_nil, reduceCtorEq] at pathHead
  | cons start tail =>
    have same : start = oldStart := Option.some.inj pathHead
    subst start
    obtain ⟨posts, liftedFinal, liftedLength, liftedChain, liftedLast, finalRep, frame⟩ :=
      Native.Lift.path (embed valueMode) Query.localDrain before oldStart oldFinal tail
        representation pathChain pathLast
    have liftedHalt : TM2.step (Native.Lift.machine (embed valueMode) Query.localDrain) liftedFinal = none := by
      apply Native.Lift.halt_project
      rw [finalRep]
      rfl
    have agrees : ∀ label : TwoStack.Label,
        program valueMode ((fun _ : TwoStack.Label => (0 : Label)) label) =
          Native.Inline.statement (fun _ : TwoStack.Label => (0 : Label)) 1
            (Native.Lift.machine (embed valueMode) Query.localDrain label) := by intro label; rfl
    obtain ⟨run, after, head, chain, last, returned, data, localStoreEq, length⟩ :=
      Native.Inline.actual_return_trace (fun _ : TwoStack.Label => (0 : Label)) 1
        (Native.Lift.machine (embed valueMode) Query.localDrain) (program valueMode) agrees
        (before :: posts) before liftedFinal store.2 rfl liftedChain liftedLast liftedHalt
    have primary : liftedFinal.var = none := by
      exact congrArg (fun current : TwoStack.State => current.var) finalRep
    have callerStoreEq : after.var = (none, store.2) := by rw [localStoreEq, primary]
    have projected (index : TwoStack.Stack) :
        liftedFinal.stk (embed valueMode index) = oldFinal.stk index := by
      exact congrArg (fun current : TwoStack.State => current.stk index) finalRep
    have contentsEq : after.stk = slots valueMode [] (word.reverse ++ rest) other := by
      rw [data]
      funext index
      have outsideFrame := frame index
      cases valueMode <;> fin_cases index
      all_goals first
        | simpa [slots, source, target, embed, oldFinal, TwoStack.stackContents] using projected 0
        | simpa [slots, source, target, embed, oldFinal, TwoStack.stackContents] using projected 1
        | simpa [slots, source, target, embed, oldFinal, oldOther, before, TwoStack.stackContents] using projected 2
        | simpa [before, slots, source, target] using outsideFrame (by intro localIndex; fin_cases localIndex <;> decide)
    have afterEq : after = state valueMode (some 1) (none, store.2) [] (word.reverse ++ rest) other := by
      rcases after with ⟨label, vars, contents⟩
      change label = some 1 at returned
      change vars = (none, store.2) at callerStoreEq
      change contents = slots valueMode [] (word.reverse ++ rest) other at contentsEq
      subst label
      subst vars
      subst contents
      rfl
    refine ⟨run, ?_, chain, ?_, ?_⟩
    · exact head
    · simpa only [afterEq] using last
    · simp only [List.length_cons] at length pathLength
      omega

/-- Full concrete source subroutine, including its actual final halt. -/
theorem drain_runs (valueMode : Bool) (word rest : List Bool) (other : Stack → List Bool) (store : Store) :
    ∃ (run : List State) (after : State),
      run.head? = some (state valueMode (some 0) store word rest other) ∧
      run.IsChain (fun a b => TM2.step (program valueMode) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program valueMode) after = none ∧
      after.l = none ∧ after.var = (none, store.2) ∧
      after.stk = slots valueMode [] (word.reverse ++ rest) other ∧
      run.length = word.length + 3 := by
  obtain ⟨path, head, chain, last, length⟩ := return_run valueMode word rest other store
  let after := state valueMode none (none, store.2) [] (word.reverse ++ rest) other
  let run := path ++ [after]
  have actual : run.IsChain (fun a b => TM2.step (program valueMode) a = some b) := by
    apply chain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [last, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old
    subst next
    rfl
  refine ⟨run, after, ?_, actual, List.getLast?_append_cons path after [], rfl, rfl, rfl, rfl, ?_⟩
  · change (path ++ [after]).head? = _
    simp only [List.head?_append, head, Option.some_or]
  · simp only [run, List.length_append, List.length_cons, List.length_nil, length]

end PDROC.BitVM.Log.Drain
