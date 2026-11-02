module

public import Paid.PDROC_D27Prepare_Resources_003
public import Paid.PDROC_D27Prepare_Resources_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits

namespace PDROC.D27Prepare.Resources

def lengthBudget (P : Parameters) (fee : ℚ) : ℕ := 4096 * (dataWeight P fee + 1) ^ 2

theorem lengthBudget_polynomial : PolynomialBound size (fun x => lengthBudget x.1 x.2) := by
  have h := dataWeight_polynomial.add (PolynomialBound.constant size 1) size_pos
  have hp : PolynomialBound size (fun x => (dataWeight x.1 x.2 + 1) ^ 2) := by
    convert h.mul h using 1
    funext x
    ring
  exact (PolynomialBound.constant size 4096).mul hp

/-- One C and one degree serve all three original resources. Constants
are chosen before P and fee; no fee-dependent coefficient is introduced. -/
theorem common_polynomial_envelope :
    ∃ C degree : ℕ, 0 < C ∧ ∀ P fee,
      15 * lengthBudget P fee ≤ C * (variableGammaSize P fee) ^ degree ∧
      84 ≤ C * (variableGammaSize P fee) ^ degree ∧
      operandBudget P fee + 21 ≤ C * (variableGammaSize P fee) ^ degree := by
  have ht := (PolynomialBound.constant size 15).mul lengthBudget_polynomial
  have hc := PolynomialBound.constant size 84
  have hb := operandBudget_polynomial.add (PolynomialBound.constant size 21) size_pos
  obtain ⟨C, degree, positive, bounded⟩ := (ht.add hc size_pos).add hb size_pos
  refine ⟨C, degree, positive, ?_⟩
  intro P fee
  have common := bounded (P, fee)
  change 15 * lengthBudget P fee + 84 + (operandBudget P fee + 21) ≤
    C * (variableGammaSize P fee) ^ degree at common
  omega

/-- Final resource assembly. The caller still has to supply the actual
fixed-program Runs, exact prepared13 output, actual trace length and every
physical prefix invariant; none of these is inferred from data bounds. -/
theorem prepare_resources_of_bounded_traces (prepare : Program) (code : prepare.size = 11776)
    (traces : ∀ (P : Parameters) (fee : ℚ), 0 ≤ fee →
      ∃ (trace : List State) (final : State), Runs prepare (rawInput P fee) trace final ∧
        final.output = preparedInput P fee ∧ trace.length ≤ lengthBudget P fee ∧
        (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
        (∀ state ∈ trace, state.output.length ≤ 13)) :
    ∃ C degree : ℕ, 0 < C ∧ ∀ (P : Parameters) (fee : ℚ), 0 ≤ fee →
      ∃ (trace : List State) (final : State), Runs prepare (rawInput P fee) trace final ∧
        final.output = preparedInput P fee ∧
        time prepare trace ≤ C * (variableGammaSize P fee) ^ degree ∧
        peakCells trace ≤ C * (variableGammaSize P fee) ^ degree ∧
        peakOperandBits trace ≤ C * (variableGammaSize P fee) ^ degree := by
  obtain ⟨C, degree, positive, envelope⟩ := common_polynomial_envelope
  refine ⟨C, degree, positive, ?_⟩
  intro P fee nonnegative
  obtain ⟨trace, final, run, output, length, values, outputLength⟩ := traces P fee nonnegative
  have actual := fixed_prepare_trace_resources prepare (rawInput P fee) trace final run code
    (lengthBudget P fee) (operandBudget P fee) length
    (fun state member => (values state member).live) outputLength
    (fun state member => (values state member).registers)
    (fun state member => (values state member).heapValues)
    (fun state member => (values state member).outputs)
  obtain ⟨ht, hc, hb⟩ := envelope P fee
  exact ⟨trace, final, run, output, actual.1.trans ht, actual.2.1.trans hc, actual.2.2.trans hb⟩

end PDROC.D27Prepare.Resources
