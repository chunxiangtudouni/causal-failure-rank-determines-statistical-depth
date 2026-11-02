module

public import Paid.PDROC_BitVM_Log_Query_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! Proof witnesses and mathematical postconditions for the literal per-Bool
loop. `afterStore` contains a List-equality SPECIFICATION, not a function used
anywhere in `program`, its store updates or its transitions. -/

namespace PDROC.BitVM.Log.Query

open Turing

def afterStore (address query : List Bool) (store : Store) : Store :=
  (none, ((query.drop address.length).head?,
    (equality store && decide (address = query), recordTag store)))

def loopTrace (other : Stack → List Bool) :
    List Bool → List Bool → List Bool → Store → List State
  | [], query, saved, store =>
      [state (some 1) store [] query saved other,
       state (some 2) (compareEnd (setQuery (setRecord store none) query.head?)) [] query saved other]
  | left :: address, [], saved, store =>
      state (some 1) store (left :: address) [] saved other ::
        loopTrace other address [] saved (compareSymbol (setQuery (setRecord store (some left)) none))
  | left :: address, right :: query, saved, store =>
      state (some 1) store (left :: address) (right :: query) saved other ::
        loopTrace other address query (right :: saved)
          (compareSymbol (setQuery (setRecord store (some left)) (some right)))

theorem loop_trace_head (address query saved : List Bool) (other : Stack → List Bool) (store : Store) :
    (loopTrace other address query saved store).head? =
      some (state (some 1) store address query saved other) := by
  cases address <;> cases query <;> rfl

theorem loop_trace_length (address query saved : List Bool) (other : Stack → List Bool) (store : Store) :
    (loopTrace other address query saved store).length = address.length + 2 := by
  induction address generalizing query saved store with
  | nil => rfl
  | cons left address ih => cases query <;> simp only [loopTrace, List.length_cons, ih]

theorem loop_trace_chain (address query saved : List Bool) (other : Stack → List Bool) (store : Store) :
    (loopTrace other address query saved store).IsChain
      (fun before after => TM2.step program before = some after) := by
  induction address generalizing query saved store with
  | nil =>
    apply List.isChain_cons_cons.mpr
    exact ⟨compare_end query saved other store, List.isChain_singleton _⟩
  | cons left address ih =>
    cases query with
    | nil =>
      change (_ :: loopTrace other address [] saved
        (compareSymbol (setQuery (setRecord store (some left)) none))).IsChain _
      apply List.IsChain.cons (ih [] saved _)
      intro after member
      rw [loop_trace_head] at member
      have equal := Option.mem_some_iff.mp member
      subst after
      exact compare_missing_query left address saved other store
    | cons right query =>
      change (_ :: loopTrace other address query (right :: saved)
        (compareSymbol (setQuery (setRecord store (some left)) (some right)))).IsChain _
      apply List.IsChain.cons (ih query (right :: saved) _)
      intro after member
      rw [loop_trace_head] at member
      have equal := Option.mem_some_iff.mp member
      subst after
      exact compare_some left right address query saved other store

theorem afterStore_nil (query : List Bool) (store : Store) :
    afterStore [] query store = compareEnd (setQuery (setRecord store none) query.head?) := by
  cases query <;> simp [afterStore, compareEnd, setRecord, setQuery, setEquality,
    equality, querySymbol, recordTag]

theorem afterStore_missing_query (left : Bool) (address : List Bool) (store : Store) :
    afterStore (left :: address) [] store =
      afterStore address [] (compareSymbol (setQuery (setRecord store (some left)) none)) := by
  simp [afterStore, compareSymbol, setRecord, setQuery, setEquality, equality, querySymbol, recordTag]

theorem afterStore_cons (left right : Bool) (address query : List Bool) (store : Store) :
    afterStore (left :: address) (right :: query) store =
      afterStore address query
        (compareSymbol (setQuery (setRecord store (some left)) (some right))) := by
  simp [afterStore, compareSymbol, setRecord, setQuery, setEquality, equality,
    querySymbol, recordTag, Bool.and_assoc]

theorem loop_trace_last (address query saved : List Bool) (other : Stack → List Bool) (store : Store) :
    (loopTrace other address query saved store).getLast? =
      some (state (some 2) (afterStore address query store) []
        (query.drop address.length) ((query.take address.length).reverse ++ saved) other) := by
  induction address generalizing query saved store with
  | nil => simp [loopTrace, afterStore_nil]
  | cons left address ih =>
    cases query with
    | nil =>
      rw [loopTrace, List.getLast?_cons, ih]
      simp only [Option.getD_some, List.drop_nil, List.take_nil, List.reverse_nil,
        List.nil_append, afterStore_missing_query]
    | cons right query =>
      rw [loopTrace, List.getLast?_cons, ih]
      simp only [Option.getD_some, List.length_cons, List.drop_succ_cons,
        List.take_succ_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, afterStore_cons]

end PDROC.BitVM.Log.Query
