module

public import Paid.PDROC_D27Prepare_Output_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid.Computation

namespace PDROC.D27Prepare.Prefix

/-- A chain ending at the cut cannot have executed an earlier state at
or above it when every successful step there strictly increases PC. -/
theorem chain_pc_cut (program : Program) (input : List Cell) (cut : ℕ)
    (forward : ∀ before after, step program input before = some after →
      cut ≤ before.pc → before.pc < after.pc) :
    ∀ (trace : List State) (final : State),
      trace.IsChain (fun a b => step program input a = some b) →
      trace.getLast? = some final → final.pc = cut →
      (∀ state ∈ trace, state.pc ≤ cut) ∧
      (∀ state ∈ trace.dropLast, state.pc < cut) := by
  intro trace
  induction trace with
  | nil => intro final chain last atCut; simp at last
  | cons before tail ih =>
      intro final chain last atCut
      cases tail with
      | nil =>
          have same : before = final := Option.some.inj last
          subst final
          constructor
          · intro state member
            have equal := List.mem_singleton.mp member
            subst state
            exact atCut.le
          · intro state member
            simp at member
      | cons middle rest =>
          have parts := List.isChain_cons_cons.mp chain
          have later := ih final parts.2 (by simpa only [List.getLast?_cons_cons] using last) atCut
          have middleBound := later.1 middle (by simp)
          have beforeBound : before.pc < cut := by
            by_contra notBelow
            have progressed := forward before middle parts.1 (by omega)
            omega
          constructor
          · intro state member
            rcases List.mem_cons.mp member with same | member
            · subst state; exact beforeBound.le
            · exact later.1 state member
          · intro state member
            rw [List.dropLast_cons_cons] at member
            rcases List.mem_cons.mp member with same | member
            · subst state; exact beforeBound
            · exact later.2 state member

theorem primitiveTrace_eq_of_code_agreement (oldProgram newProgram : Program) (cut : ℕ)
    (same : ∀ address < cut, oldProgram[address]? = newProgram[address]?) :
    ∀ trace : List State, (∀ state ∈ trace, state.pc < cut) →
      primitiveTrace oldProgram trace = primitiveTrace newProgram trace := by
  intro trace
  induction trace with
  | nil => intro bounds; rfl
  | cons state rest ih =>
      intro bounds
      change ((oldProgram[state.pc]?).map Instruction.primitives).getD [] ++ primitiveTrace oldProgram rest =
        ((newProgram[state.pc]?).map Instruction.primitives).getD [] ++ primitiveTrace newProgram rest
      rw [same state.pc (bounds state (by simp)), ih (fun other member => bounds other (List.mem_cons_of_mem state member))]

/-- Empty output is a consequence of the actual append-only chain, not
an instruction that erases a previously emitted standalone prepared13. -/
theorem outputs_empty (program : Program) (input : List Cell) (trace : List State) (final : State)
    (chain : trace.IsChain (fun a b => step program input a = some b))
    (last : trace.getLast? = some final) (empty : final.output = []) :
    ∀ state ∈ trace, state.output = [] := by
  intro state member
  have earlier := Output.chain_prefix_final program input trace final chain last state member
  rw [empty] at earlier
  exact List.prefix_nil.mp earlier

end PDROC.D27Prepare.Prefix
