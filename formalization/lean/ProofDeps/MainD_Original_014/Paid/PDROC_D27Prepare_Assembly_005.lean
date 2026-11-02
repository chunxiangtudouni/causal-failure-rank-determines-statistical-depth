module

public import Paid.PDROC_D27Prepare_001
public import Paid.PDROC_D27Prepare_Assembly_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Assembly

/-- The original fixed program, including its thirteen actual outputs and
fetched HALT, runs from raw6 with every physical prefix bounded. -/
theorem raw_prepare_bounded_trace (P : Parameters) (fee : ℚ) :
    ∃ (trace : List State) (final : State), Runs program (rawInput P fee) trace final ∧
      final.output = preparedInput P fee ∧ trace.length ≤ lengthBudget P fee ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      (∀ state ∈ trace, state.output.length ≤ 13) := by
  obtain ⟨before, earlier, preFinal, earlierHead, earlierLast, earlierChain,
    earlierLength, earlierBounds⟩ := raw_preFinal_trace P fee
  let memory := Search.currentMemory before
  have matched : MemoryMatch before memory := Search.currentMemory_match before preFinal.fresh
  have live (address : ℕ) (inside : address < 13) : address ∈ memory.present := by
    rw [← matched.live]
    exact PreparedMemory.live P fee before preFinal.cells address inside
  obtain ⟨final, later, _, emitted, laterHead, laterLast, laterLength, laterChain, halt, _, laterBounds⟩ :=
    bounded_emitPrepared_trace (rawInput P fee) before memory (operandBudget P fee) matched
      preFinal.location preFinal.bounded live (operandBudget_address_bits P fee)
  have output : final.output = preparedInput P fee := by
    rw [emitted, preFinal.output, List.nil_append]
    exact PreparedMemory.row P fee before preFinal.cells
  let trace := joinTrace earlier later
  have head := joinTrace_head earlier later initial before earlierHead earlierLast laterHead
  have last := joinTrace_last earlier later final laterLast
  have chain := joinTrace_chain program (rawInput P fee) earlier later before earlierChain laterChain earlierLast laterHead
  have run : Runs program (rawInput P fee) trace final := runs_of_actual_trace (rawInput P fee) trace final head chain last halt
  refine ⟨trace, final, run, output, ?_, ?_, ?_⟩
  · apply linear_length_budget P fee
    simp only [trace, joinTrace, List.length_append, List.length_dropLast]
    omega
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact earlierBounds state (List.mem_of_mem_dropLast early)
    · exact laterBounds state late
  · intro state member
    exact (Output.prepared_all_prefixes program P fee trace final run output state member).1

theorem exact_prepare_claims : ExactPrepareClaims := by
  obtain ⟨C, degree, positive, bounded⟩ := prepare_resources_of_bounded_traces program program_size
    (fun P fee _ => raw_prepare_bounded_trace P fee)
  exact ⟨program, C, degree, positive, bounded⟩

end PDROC.D27Prepare.Assembly
