module

public import Paid.PDROC_D27Prepare_Assembly_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Assembly

/-- A core may replace the continuation at pc45.  This certificate keeps
the actual raw execution, all scratch state, exact prepared heap, and
strict code provenance for every executed state of the prefix. -/
theorem raw_preFinal_certificate :
    ∃ C degree : ℕ, 0 < C ∧ ∀ (P : Parameters) (fee : ℚ),
      ∃ (final : State) (trace : List State), PreFinalState P fee final ∧
        trace.head? = some initial ∧ trace.getLast? = some final ∧
        trace.IsChain (fun a b => step program (rawInput P fee) a = some b) ∧
        (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
        (∀ state ∈ trace, state.output = []) ∧
        (∀ state ∈ trace.dropLast, state.pc < pc 45) ∧
        time program trace ≤ C * (variableGammaSize P fee) ^ degree ∧
        peakCells trace ≤ C * (variableGammaSize P fee) ^ degree ∧
        peakOperandBits trace ≤ C * (variableGammaSize P fee) ^ degree := by
  obtain ⟨C, degree, positive, envelope⟩ := common_polynomial_envelope
  refine ⟨C, degree, positive, ?_⟩
  intro P fee
  obtain ⟨final, trace, preFinal, head, last, chain, length, bounds⟩ := raw_preFinal_trace P fee
  have actual := preFinal_resources P fee trace final preFinal chain last
    (linear_length_budget P fee trace.length (by omega)) bounds
  obtain ⟨ht, hc, hb⟩ := envelope P fee
  exact ⟨final, trace, preFinal, head, last, chain, bounds,
    Prefix.outputs_empty program (rawInput P fee) trace final chain last preFinal.output,
    Prefix.preFinal_trace_pc (rawInput P fee) trace final chain last preFinal.location,
    actual.1.trans ht, actual.2.1.trans hc, actual.2.2.trans hb⟩

end PDROC.D27Prepare.Assembly
