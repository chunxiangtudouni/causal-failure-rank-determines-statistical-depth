module

public import Paid.PDROC_BitVM_Log_Capture_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Capture

open Turing

def slots (input ticks archive captured : List Bool) (other : Stack → List Bool) : Stack → List Bool :=
  fun stack => if stack = 0 then input else if stack = 1 then ticks
    else if stack = 2 then archive else if stack = 6 then captured else other stack

def state (label : Option Label) (store : Store) (input ticks archive captured : List Bool)
    (other : Stack → List Bool) : State := ⟨label, store, slots input ticks archive captured other⟩

theorem update_input (input ticks archive captured replacement : List Bool) (other : Stack → List Bool) :
    Function.update (slots input ticks archive captured other) 0 replacement =
      slots replacement ticks archive captured other := by
  funext stack; fin_cases stack <;> simp [slots]

theorem update_ticks (input ticks archive captured replacement : List Bool) (other : Stack → List Bool) :
    Function.update (slots input ticks archive captured other) 1 replacement =
      slots input replacement archive captured other := by
  funext stack; fin_cases stack <;> simp [slots]

theorem update_archive (input ticks archive captured replacement : List Bool) (other : Stack → List Bool) :
    Function.update (slots input ticks archive captured other) 2 replacement =
      slots input ticks replacement captured other := by
  funext stack; fin_cases stack <;> simp [slots]

theorem update_captured (input ticks archive captured replacement : List Bool) (other : Stack → List Bool) :
    Function.update (slots input ticks archive captured other) 6 replacement =
      slots input ticks archive replacement other := by
  funext stack; fin_cases stack <;> simp [slots]

theorem header_true (input ticks archive captured : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some 0) store (true :: input) ticks archive captured other) =
      some (state (some 0) (Query.setRecord store (some true)) input
        (true :: ticks) (true :: archive) (true :: captured) other) := by
  change (some ⟨some 0, Query.setRecord store (some true),
    Function.update (Function.update (Function.update (Function.update
      (slots (true :: input) ticks archive captured other) 0 input)
      2 (true :: archive)) 6 (true :: captured)) 1 (true :: ticks)⟩ : Option State) = _
  rw [update_input, update_archive, update_captured, update_ticks]
  rfl

theorem header_false (input ticks archive captured : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some 0) store (false :: input) ticks archive captured other) =
      some (state (some 1) (Query.setRecord store (some false)) input
        ticks (false :: archive) (false :: captured) other) := by
  change (some ⟨some 1, Query.setRecord store (some false),
    Function.update (Function.update (Function.update
      (slots (false :: input) ticks archive captured other) 0 input)
      2 (false :: archive)) 6 (false :: captured)⟩ : Option State) = _
  rw [update_input, update_archive, update_captured]
  rfl

theorem header_eof (ticks archive captured : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some 0) store [] ticks archive captured other) =
      some (state (some 4) (Query.setRecord store none) [] ticks archive captured other) := by
  change (some ⟨some 4, Query.setRecord store none,
    Function.update (slots [] ticks archive captured other) 0 []⟩ : Option State) = _
  rw [update_input]
  rfl

theorem payload_bit (bit : Bool) (input ticks archive captured : List Bool)
    (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some 1) store (bit :: input) (true :: ticks) archive captured other) =
      some (state (some 1) (Query.setRecord store (some bit)) input ticks
        (bit :: archive) (bit :: captured) other) := by
  change (some ⟨some 1, Query.setRecord store (some bit),
    Function.update (Function.update (Function.update (Function.update
      (slots (bit :: input) (true :: ticks) archive captured other) 1 ticks) 0 input)
      2 (bit :: archive)) 6 (bit :: captured)⟩ : Option State) = _
  rw [update_ticks, update_input, update_archive, update_captured]
  rfl

theorem payload_done (input archive captured : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some 1) store input [] archive captured other) =
      some (state (some 2) (Query.setRecord store none) input [] archive captured other) := by
  change (some ⟨some 2, Query.setRecord store none,
    Function.update (slots input [] archive captured other) 1 []⟩ : Option State) = _
  rw [update_ticks]
  rfl

theorem payload_eof (ticks archive captured : List Bool) (other : Stack → List Bool) (store : Store) :
    TM2.step program (state (some 1) store [] (true :: ticks) archive captured other) =
      some (state (some 4) (Query.setRecord store none) [] ticks archive captured other) := by
  change (some ⟨some 4, Query.setRecord store none,
    Function.update (Function.update (slots [] (true :: ticks) archive captured other) 1 ticks) 0 []⟩ : Option State) = _
  rw [update_ticks, update_input]
  rfl

end PDROC.BitVM.Log.Capture
