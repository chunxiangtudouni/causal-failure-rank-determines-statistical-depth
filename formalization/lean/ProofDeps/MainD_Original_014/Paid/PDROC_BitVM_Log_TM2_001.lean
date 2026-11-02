module

public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.List.Chain
public import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! A genuine fixed finite-control Boolean-stack drain. It reads at most one
Bool and executes a bounded literal pop/branch/push/goto statement per step.
The mathematical trace is a proof witness, not part of the machine state. -/

namespace PDROC.BitVM.Log.TwoStack

open Turing

abbrev Stack := Fin 3
abbrev Label := Fin 3
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Option Bool
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def drain (source target : Stack) (again : Label) (finish : Statement) : Statement :=
  .pop source (fun _ symbol => symbol)
    (.branch Option.isSome
      (.push target (fun symbol => symbol.getD false) (.goto (fun _ => again))) finish)

/-- Stack 0 is a record workspace, 1 temporary, and 2 the existing log. -/
def program (label : Label) : Statement :=
  if label = 0 then drain 0 1 0 (.goto (fun _ => 1))
  else if label = 1 then drain 1 2 1 .halt
  else .halt

def stackContents (source target : Stack) (word archive : List Bool)
    (other : Stack → List Bool) : Stack → List Bool :=
  fun stack => if stack = source then word else if stack = target then archive else other stack

def state (source target : Stack) (label : Label) (store : Store)
    (word archive : List Bool) (other : Stack → List Bool) : State :=
  ⟨some label, store, stackContents source target word archive other⟩

theorem update_source (source target : Stack) (word archive replacement : List Bool)
    (other : Stack → List Bool) :
    Function.update (stackContents source target word archive other) source replacement =
      stackContents source target replacement archive other := by
  funext stack
  by_cases same : stack = source <;> simp [stackContents, same]

theorem update_target (source target : Stack) (different : target ≠ source)
    (word archive replacement : List Bool) (other : Stack → List Bool) :
    Function.update (stackContents source target word archive other) target replacement =
      stackContents source target word replacement other := by
  funext stack
  by_cases sameSource : stack = source
  · subst stack; simp [stackContents, Ne.symm different]
  · by_cases sameTarget : stack = target
    · subst stack; simp [stackContents, different]
    · simp [stackContents, sameSource, sameTarget]

theorem drain_cons (source target : Stack) (different : target ≠ source)
    (label : Label) (finish : Statement) (store : Store) (bit : Bool)
    (word archive : List Bool) (other : Stack → List Bool) :
    TM2.stepAux (drain source target label finish) store
      (stackContents source target (bit :: word) archive other) =
      state source target label (some bit) word (bit :: archive) other := by
  have sourceRead : stackContents source target (bit :: word) archive other source = bit :: word :=
    by simp [stackContents]
  have targetRead : stackContents source target (bit :: word) archive other target = archive :=
    by simp [stackContents, different]
  simp only [drain, TM2.stepAux, sourceRead, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some, Bool.cond_true]
  rw [Function.update_of_ne different, targetRead, update_source,
    update_target source target different]
  rfl

theorem drain_nil (source target : Stack) (label : Label) (finish : Statement)
    (store : Store) (archive : List Bool) (other : Stack → List Bool) :
    TM2.stepAux (drain source target label finish) store (stackContents source target [] archive other) =
      TM2.stepAux finish none (stackContents source target [] archive other) := by
  have sourceRead : stackContents source target [] archive other source = [] := by simp [stackContents]
  simp only [drain, TM2.stepAux, sourceRead, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  rw [update_source]

def trace (source target : Stack) (label : Label) (finish : Statement)
    (other : Stack → List Bool) : List Bool → List Bool → Store → List State
  | [], archive, store =>
      [state source target label store [] archive other,
       TM2.stepAux finish none (stackContents source target [] archive other)]
  | bit :: word, archive, store =>
      state source target label store (bit :: word) archive other ::
        trace source target label finish other word (bit :: archive) (some bit)

theorem trace_head (source target : Stack) (label : Label) (finish : Statement)
    (other : Stack → List Bool) (word archive : List Bool) (store : Store) :
    (trace source target label finish other word archive store).head? =
      some (state source target label store word archive other) := by
  cases word <;> rfl

theorem trace_last (source target : Stack) (label : Label) (finish : Statement)
    (other : Stack → List Bool) (word archive : List Bool) (store : Store) :
    (trace source target label finish other word archive store).getLast? =
      some (TM2.stepAux finish none
        (stackContents source target [] (word.reverse ++ archive) other)) := by
  induction word generalizing archive store with
  | nil => rfl
  | cons bit word ih =>
    rw [trace, List.getLast?_cons, ih]
    simp only [Option.getD_some, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem trace_length (source target : Stack) (label : Label) (finish : Statement)
    (other : Stack → List Bool) (word archive : List Bool) (store : Store) :
    (trace source target label finish other word archive store).length = word.length + 2 := by
  induction word generalizing archive store with
  | nil => rfl
  | cons bit word ih => simp only [trace, List.length_cons, ih]

theorem trace_chain (machine : Label → Statement) (source target : Stack)
    (different : target ≠ source) (label : Label) (finish : Statement)
    (code : machine label = drain source target label finish)
    (other : Stack → List Bool) (word archive : List Bool) (store : Store) :
    (trace source target label finish other word archive store).IsChain
      (fun before after => TM2.step machine before = some after) := by
  induction word generalizing archive store with
  | nil =>
    apply List.isChain_cons_cons.mpr
    constructor
    · change some (TM2.stepAux (machine label) store _) = _
      rw [code, drain_nil]
    · exact List.isChain_singleton _
  | cons bit word ih =>
    change (_ :: trace source target label finish other word (bit :: archive) (some bit)).IsChain _
    apply List.IsChain.cons (ih (bit :: archive) (some bit))
    intro after member
    rw [trace_head] at member
    have equal : after = state source target label (some bit) word (bit :: archive) other :=
      (Option.mem_some_iff.mp member).symm
    subst after
    change some (TM2.stepAux (machine label) store _) = _
    rw [code, drain_cons source target different]

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label <;> simp [program, drain, TM2.SupportsStmt]

end PDROC.BitVM.Log.TwoStack
