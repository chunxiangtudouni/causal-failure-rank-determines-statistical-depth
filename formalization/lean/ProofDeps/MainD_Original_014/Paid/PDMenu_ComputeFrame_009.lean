module

public import Paid.PDMenu_ComputeFrame_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation

theorem step_memoryFrame (region : Finset ℕ) (program : Program) (input : List Cell) (before after : State)
    (safe : ∀ instruction, program[before.pc]?=some instruction → WritesWithin region instruction before)
    (run : step program input before=some after) : MemoryFrame region before after := by
  obtain ⟨instruction,fetched,executed⟩ := Option.bind_eq_some_iff.mp run
  exact execute_memoryFrame region instruction input before after (safe instruction fetched) executed

/-- Every real intermediate state receives its OWN frame by induction
over the actual original step chain. Safety is checked only at fetched
preterminal states, so an arbitrary caller's final return fetch is free
to have different code. No final-state frame is assumed. -/
theorem chain_memoryFrames (region : Finset ℕ) (program : Program) (input : List Cell)
    (trace : List State) (before : State) (head : trace.head?=some before)
    (chain : trace.IsChain (fun first later => step program input first=some later))
    (safe : ∀ state ∈ trace.dropLast, ∀ instruction,
      program[state.pc]?=some instruction → WritesWithin region instruction state) :
    ∀ state ∈ trace, MemoryFrame region before state := by
  induction trace generalizing before with
  | nil => simp at head
  | cons first tail ih =>
    have he : first=before := Option.some.inj head
    subst first
    cases tail with
    | nil =>
      intro state member
      have he : state=before := List.mem_singleton.mp member
      subst state
      exact MemoryFrame.refl region before
    | cons middle rest =>
      have hc := List.isChain_cons_cons.mp chain
      have hf : MemoryFrame region before middle := step_memoryFrame region program input before middle
        (safe before (by simp)) hc.1
      have later := ih middle rfl hc.2 (by
        intro state member instruction fetched
        exact safe state (by simp only [List.dropLast_cons_cons,List.mem_cons]; exact Or.inr member) instruction fetched)
      intro state member
      rcases List.mem_cons.mp member with same|member
      · subst state
        exact MemoryFrame.refl region before
      · exact hf.trans (later state member)

theorem MemoryFrame.live_subset {region : Finset ℕ} {before after : State}
    (frame : MemoryFrame region before after) : after.live ⊆ before.live ∪ region := by
  intro address member
  by_cases inside : address ∈ region
  · exact Finset.mem_union.mpr (Or.inr inside)
  · exact Finset.mem_union.mpr (Or.inl ((frame.2 address inside).mp member))

theorem MemoryFrame.live_card_le {region : Finset ℕ} {before after : State}
    (frame : MemoryFrame region before after) : after.live.card ≤ before.live.card+region.card :=
  (Finset.card_le_card frame.live_subset).trans (Finset.card_union_le _ _)

theorem MemoryFrame.workingCells_le {region : Finset ℕ} {before after : State}
    (frame : MemoryFrame region before after) (extra : ℕ)
    (output : after.output.length ≤ before.output.length+extra) :
    workingCells after ≤ workingCells before+region.card+extra := by
  have live := frame.live_card_le
  simp only [workingCells]
  omega

end PDMenu.ComputeFrame
