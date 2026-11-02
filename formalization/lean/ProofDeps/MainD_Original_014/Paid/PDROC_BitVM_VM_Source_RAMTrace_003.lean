module

public import Paid.PDROC_BitVM_Kernel_Nop_050

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.VM.Source

open PaperProofs.Paid.Computation

/-- A successful original source edge already supplies a valid fetch.
This is derived from the original step; it is never a new qualification
on the input or a host PC conversion used in a transition. -/
theorem fetch_of_step (code : Program) (input : List Cell) (before after : State)
    (actual : step code input before = some after) :
    ∃ instruction, code[before.pc]? = some instruction ∧ instruction.execute input before = some after := by
  cases fetched : code[before.pc]? with
  | none => simp [step,fetched] at actual
  | some instruction =>
    exact ⟨instruction,rfl,by simpa [step,fetched] using actual⟩

theorem pc_valid_of_step (code : Program) (input : List Cell) (before after : State)
    (actual : step code input before = some after) : before.pc < code.size := by
  obtain ⟨instruction,fetched,_execute⟩ := fetch_of_step code input before after actual
  exact (Array.getElem?_eq_some_iff.mp fetched).1

theorem pc_valid_of_fetched_halt (code : Program) (final : State)
    (fetched : code[final.pc]? = some .halt) : final.pc < code.size :=
  (Array.getElem?_eq_some_iff.mp fetched).1

/-- Every prefix PC, including the final fetched halt, is valid on the
same original RAM path. No extra good-input predicate is introduced. -/
theorem chain_pc_valid (code : Program) (input : List Cell) (trace : List State) (final : State)
    (chain : trace.IsChain (fun a b => step code input a = some b))
    (last : trace.getLast? = some final) (halt : code[final.pc]? = some .halt) :
    ∀ state ∈ trace, state.pc < code.size := by
  induction trace with
  | nil => simp
  | cons first rest ih =>
    cases rest with
    | nil =>
      have same : first = final := Option.some.inj last
      subst first
      intro state member
      have same : state = final := List.mem_singleton.mp member
      subst state
      exact pc_valid_of_fetched_halt code final halt
    | cons next later =>
      have edge := (List.isChain_cons_cons.mp chain).1
      have tailChain := (List.isChain_cons_cons.mp chain).2
      have tailLast : (next::later).getLast? = some final := by
        simpa only [List.getLast?_cons_cons] using last
      intro state member
      rcases List.mem_cons.mp member with same | inTail
      · subst state
        exact pc_valid_of_step code input first next edge
      · exact ih tailChain tailLast state inTail

theorem runs_pc_valid (code : Program) (input : List Cell) (trace : List State) (final : State)
    (actual : Runs code input trace final) : ∀ state ∈ trace, state.pc < code.size :=
  chain_pc_valid code input trace final actual.2.1 actual.2.2.1 actual.2.2.2.1

theorem runs_code_nonempty (code : Program) (input : List Cell) (trace : List State) (final : State)
    (actual : Runs code input trace final) : 0 < code.size := by
  have valid := pc_valid_of_fetched_halt code final actual.2.2.2.1
  omega

end PDROC.BitVM.VM.Source
