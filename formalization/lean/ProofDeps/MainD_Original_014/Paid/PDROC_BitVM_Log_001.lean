module

public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! Specification of source heap history only. No definition in this file is
an implementation by a Boolean Turing machine. In particular `lookup` is a
mathematical interpretation and is never a TM variable or transition. -/

namespace PDROC.BitVM.Log

open PaperProofs.Paid.Computation

structure HeapEvent where
  address : ℕ
  value : Option Cell
  deriving DecidableEq

/-- Chronological replay. A tombstone overwrites an older `some` by `none`. -/
def replay (cells : ℕ → Option Cell) (event : HeapEvent) : ℕ → Option Cell :=
  Function.update cells event.address event.value

def lookup (events : List HeapEvent) : ℕ → Option Cell :=
  events.foldl replay (fun _ => none)

@[simp] theorem lookup_nil (address : ℕ) : lookup [] address = none := rfl

theorem lookup_append (events : List HeapEvent) (event : HeapEvent) :
    lookup (events ++ [event]) = Function.update (lookup events) event.address event.value := by
  simp only [lookup, List.foldl_append, List.foldl_cons, List.foldl_nil, replay]

@[simp] theorem lookup_append_same (events : List HeapEvent) (event : HeapEvent) :
    lookup (events ++ [event]) event.address = event.value := by
  rw [lookup_append, Function.update_self]

theorem lookup_append_other (events : List HeapEvent) (event : HeapEvent) (address : ℕ)
    (different : address ≠ event.address) :
    lookup (events ++ [event]) address = lookup events address := by
  rw [lookup_append, Function.update_of_ne different]

def Refines (events : List HeapEvent) (state : State) : Prop :=
  (∀ address, state.heap address = (lookup events address).getD (.natural 0)) ∧
  (∀ address, address ∈ state.live ↔ (lookup events address).isSome = true)

theorem initial_refines : Refines [] initial := by
  constructor <;> intro address <;> simp [initial, lookup]

def storeState (before : State) (address : ℕ) (value : Cell) : State :=
  { before with
    heap := Function.update before.heap address value
    live := insert address before.live }

def releaseState (before : State) (address : ℕ) : State :=
  { before with
    heap := Function.update before.heap address (.natural 0)
    live := before.live.erase address }

theorem Refines.store {events : List HeapEvent} {before : State}
    (refines : Refines events before) (address : ℕ) (value : Cell) :
    Refines (events ++ [⟨address, some value⟩]) (storeState before address value) := by
  constructor
  · intro query
    by_cases same : query = address
    · subst query; simp [storeState, lookup_append]
    · simpa [storeState, lookup_append, Function.update_of_ne same] using refines.1 query
  · intro query
    by_cases same : query = address
    · subst query; simp [storeState, lookup_append]
    · simpa [storeState, lookup_append, same, Function.update_of_ne same] using refines.2 query

theorem Refines.release {events : List HeapEvent} {before : State}
    (refines : Refines events before) (address : ℕ) :
    Refines (events ++ [⟨address, none⟩]) (releaseState before address) := by
  constructor
  · intro query
    by_cases same : query = address
    · subst query; simp [releaseState, lookup_append]
    · simpa [releaseState, lookup_append, Function.update_of_ne same] using refines.1 query
  · intro query
    by_cases same : query = address
    · subst query; simp [releaseState, lookup_append]
    · simpa [releaseState, lookup_append, same, Function.update_of_ne same] using refines.2 query

theorem Refines.carry {events : List HeapEvent} {before after : State}
    (refines : Refines events before) (heap : after.heap = before.heap)
    (live : after.live = before.live) : Refines events after := by
  simpa only [Refines, heap, live] using refines

/-- The possible single event of an actual source instruction. -/
def eventOf : Instruction → State → Option HeapEvent
  | .store pointer source, before =>
      (before.register pointer).nat?.map (fun address => ⟨address, some (before.register source)⟩)
  | .release pointer, before =>
      (before.register pointer).nat?.map (fun address => ⟨address, none⟩)
  | _, _ => none

theorem eventOf_length (instruction : Instruction) (before : State) :
    (eventOf instruction before).toList.length ≤ 1 := by
  cases eventOf instruction before <;> simp

end PDROC.BitVM.Log
