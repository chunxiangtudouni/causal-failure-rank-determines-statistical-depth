module

public import Paid.PDROC_BitVM_Log_Query_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Query

open Turing

/-- Only actual work buffers1/3/4 are replaced; all history/result buffers
are arbitrary caller-carried Bool data. -/
def slots (address query saved : List Bool) (other : Stack → List Bool) : Stack → List Bool :=
  fun stack => if stack = 1 then address else if stack = 3 then query
    else if stack = 4 then saved else other stack

def state (label : Option Label) (store : Store) (address query saved : List Bool)
    (other : Stack → List Bool) : State := ⟨label, store, slots address query saved other⟩

theorem update_address (address query saved replacement : List Bool) (other : Stack → List Bool) :
    Function.update (slots address query saved other) 1 replacement = slots replacement query saved other := by
  funext stack; fin_cases stack <;> simp [slots]

theorem update_query (address query saved replacement : List Bool) (other : Stack → List Bool) :
    Function.update (slots address query saved other) 3 replacement = slots address replacement saved other := by
  funext stack; fin_cases stack <;> simp [slots]

theorem update_saved (address query saved replacement : List Bool) (other : Stack → List Bool) :
    Function.update (slots address query saved other) 4 replacement = slots address query replacement other := by
  funext stack; fin_cases stack <;> simp [slots]

theorem compare_some (left right : Bool) (address query saved : List Bool)
    (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some 1) store (left :: address) (right :: query) saved other) =
      some (state (some 1)
        (compareSymbol (setQuery (setRecord store (some left)) (some right)))
        address query (right :: saved) other) := by
  change (some ⟨some 1,
    compareSymbol (setQuery (setRecord store (some left)) (some right)),
    Function.update (Function.update (Function.update
      (slots (left :: address) (right :: query) saved other) 1 address) 3 query)
      4 (right :: saved)⟩ : Option State) = _
  rw [update_address, update_query, update_saved]
  rfl

theorem compare_missing_query (left : Bool) (address saved : List Bool)
    (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some 1) store (left :: address) [] saved other) =
      some (state (some 1) (compareSymbol (setQuery (setRecord store (some left)) none))
        address [] saved other) := by
  change (some ⟨some 1, compareSymbol (setQuery (setRecord store (some left)) none),
    Function.update (Function.update (slots (left :: address) [] saved other) 1 address) 3 []⟩ : Option State) = _
  rw [update_address, update_query]
  rfl

theorem compare_end (query saved : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some 1) store [] query saved other) =
      some (state (some 2) (compareEnd (setQuery (setRecord store none) query.head?))
        [] query saved other) := by
  change (some ⟨some 2, compareEnd (setQuery (setRecord store none) query.head?),
    Function.update (slots [] query saved other) 1 []⟩ : Option State) = _
  rw [update_address]
  rfl

theorem equality_some (store : Store) (left right : Bool) :
    equality (compareSymbol (setQuery (setRecord store (some left)) (some right))) =
      (equality store && decide (left = right)) := by
  simp [compareSymbol, setEquality, setRecord, setQuery, equality, querySymbol]

theorem equality_missing_query (store : Store) (left : Bool) :
    equality (compareSymbol (setQuery (setRecord store (some left)) none)) = false := by
  simp [compareSymbol, setEquality, setRecord, setQuery, equality, querySymbol]

theorem equality_end (store : Store) (query : List Bool) :
    equality (compareEnd (setQuery (setRecord store none) query.head?)) =
      (equality store && !query.head?.isSome) := rfl

theorem tag_compare (store : Store) : recordTag (compareSymbol store) = recordTag store := rfl
theorem tag_end (store : Store) : recordTag (compareEnd store) = recordTag store := rfl

end PDROC.BitVM.Log.Query
