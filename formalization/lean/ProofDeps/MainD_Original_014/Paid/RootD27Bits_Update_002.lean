module

public import Paid.RootD27Bits_Safe_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Bits

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

theorem SafeBits.set {state : State} {budget : ℕ} (safe : SafeBits state budget)
    (target : Register) (value : Cell) (bounded : value.bits≤budget) :
    SafeBits (state.set target value) budget := by
  apply SafeBits.of_fields
  · intro query
    by_cases same : query=target
    · subst query
      simpa only [State.set,Function.update_self] using bounded
    · simpa only [State.set,Function.update_of_ne same] using safe.register query
  · exact safe.address
  · exact safe.heap
  · exact safe.output
  · exact safe.pc

theorem SafeBits.withPC {state : State} {budget : ℕ} (safe : SafeBits state budget)
    (counter : ℕ) (bounded : natBits counter≤budget) :
    SafeBits {state with pc:=counter} budget :=
  SafeBits.of_fields _ _ safe.register safe.address safe.heap safe.output bounded

/-- Store an actually bounded cell at an actually bounded address.
Existing live cells and all untouched caller registers remain covered. -/
theorem SafeBits.store {state : State} {budget : ℕ} (safe : SafeBits state budget)
    (location : ℕ) (value : Cell) (addressBits : natBits location≤budget) (valueBits : value.bits≤budget) :
    SafeBits {state with heap:=Function.update state.heap location value,live:=insert location state.live} budget := by
  apply SafeBits.of_fields
  · exact safe.register
  · intro query member
    rcases Finset.mem_insert.mp member with same|prior
    · subst query
      exact addressBits
    · exact safe.address query prior
  · intro query member
    by_cases same : query=location
    · subst query
      simpa only [Function.update_self] using valueBits
    · have prior : query∈state.live := (Finset.mem_insert.mp member).resolve_left same
      simpa only [Function.update_of_ne same] using safe.heap query prior
  · exact safe.output
  · exact safe.pc

end RootD27.Bits
