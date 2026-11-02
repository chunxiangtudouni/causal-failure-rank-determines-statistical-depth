module

public import Paid.PDROC_BitVM_Log_001
public import Mathlib.Data.List.Induction

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! Mathematical newest-first lookup specification only. This host recursive
function is NOT a TM transition or internal store field. Its purpose is to
state the correctness target for a future real Bool address-comparison loop. -/

namespace PDROC.BitVM.Log

open PaperProofs.Paid.Computation

def lookupNewest : List HeapEvent → ℕ → Option Cell
  | [], _ => none
  | event :: older, address =>
      if address = event.address then event.value else lookupNewest older address

theorem newest_matching (event : HeapEvent) (older : List HeapEvent) :
    lookupNewest (event :: older) event.address = event.value := by
  simp [lookupNewest]

/-- A matching tombstone stops the search even when an older store exists. -/
theorem newest_tombstone (address : ℕ) (older : List HeapEvent) :
    lookupNewest (⟨address, none⟩ :: older) address = none :=
  newest_matching ⟨address, none⟩ older

theorem lookup_eq_newest (events : List HeapEvent) (address : ℕ) :
    lookup events address = lookupNewest events.reverse address := by
  induction events using List.reverseRecOn with
  | nil => rfl
  | append_singleton previous event ih =>
    rw [lookup_append]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, lookupNewest]
    by_cases same : address = event.address
    · subst address; simp
    · simpa only [Function.update_of_ne same, ite_eq_right same] using ih

theorem refines_newest (events : List HeapEvent) (state : State) :
    Refines events state ↔
      (∀ address, state.heap address = (lookupNewest events.reverse address).getD (.natural 0)) ∧
      (∀ address, address ∈ state.live ↔ (lookupNewest events.reverse address).isSome = true) := by
  simp only [Refines, lookup_eq_newest]

end PDROC.BitVM.Log
