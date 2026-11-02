module

public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.D27Prepare.Output

open PaperProofs.Paid PaperProofs.Paid.Computation

/-- The original ISA can only append to its output. -/
theorem execute_prefix (instruction : Instruction) (input : List Cell) (before after : State)
    (executed : instruction.execute input before = some after) : before.output <+: after.output := by
  cases instruction <;> simp_all [Instruction.execute, State.set, Option.bind_eq_some_iff]
  all_goals repeat' (obtain ⟨argument, equation, executed⟩ := executed)
  all_goals simp_all

theorem step_prefix (program : Program) (input : List Cell) (before after : State)
    (executed : step program input before = some after) : before.output <+: after.output := by
  obtain ⟨instruction, _, execute⟩ := Option.bind_eq_some_iff.mp executed
  exact execute_prefix instruction input before after execute

/-- Every actual prefix output is a prefix of the reached final output.
This uses the real step chain and does not infer prefix behavior from a
desired final list alone. -/
theorem chain_prefix_final (program : Program) (input : List Cell) :
    ∀ (trace : List State) (final : State),
      trace.IsChain (fun a b => step program input a = some b) →
      trace.getLast? = some final →
      ∀ state ∈ trace, state.output <+: final.output := by
  intro trace
  induction trace with
  | nil => intro _ _ _ state member; cases member
  | cons before tail ih =>
      intro final chain last state member
      cases tail with
      | nil =>
          have finalSame : before = final := Option.some.inj last
          have stateSame : state = before := List.mem_singleton.mp member
          subst state
          subst final
          exact List.prefix_rfl
      | cons after rest =>
          have parts := List.isChain_cons_cons.mp chain
          have later := ih final parts.2 (by simpa only [List.getLast?_cons_cons] using last)
          rcases List.mem_cons.mp member with same | member
          · subst state
            exact (step_prefix program input before after parts.1).trans (later after (by simp))
          · exact later state member

theorem runs_prefix_final (program : Program) (input : List Cell) (trace : List State) (final : State)
    (run : Runs program input trace final) : ∀ state ∈ trace, state.output <+: final.output :=
  chain_prefix_final program input trace final run.2.1 run.2.2.1

/-- Once the actual complete run emits prepared13, all earlier output
lengths and output-cell membership follow from actual append-only steps. -/
theorem prepared_all_prefixes (program : Program) (P : Parameters) (fee : ℚ)
    (trace : List State) (final : State) (run : Runs program (rawInput P fee) trace final)
    (output : final.output = preparedInput P fee) :
    ∀ state ∈ trace, state.output.length ≤ 13 ∧
      ∀ cell ∈ state.output, cell ∈ preparedInput P fee := by
  intro state member
  have outputPrefix := runs_prefix_final program (rawInput P fee) trace final run state member
  rw [output] at outputPrefix
  constructor
  · have length := outputPrefix.length_le
    simpa only [preparedInput, rawInput, List.length_append, List.length_cons, List.length_nil,
      Nat.reduceAdd] using length
  · exact outputPrefix.subset

end PDROC.D27Prepare.Output
