module

public import Paid.PDROC_D27Prepare_Assembly_001
public import Paid.PDROC_D27Prepare_Resources_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Assembly

theorem linear_length_budget (P : Parameters) (fee : ℚ) (length : ℕ)
    (bounded : length ≤ 1200 + 29 * P.certificate.t0 + 120 * P.certificate.M +
      40 * P.certificate.E + 129 * P.certificate.stages + 29 * P.bisectionBudget fee) :
    length ≤ lengthBudget P fee := by
  obtain ⟨hN, ht, hM, hE, _, hJ, _⟩ := scalar_data_bounds P fee
  have linear : length ≤ 4096 * (dataWeight P fee + 1) := by omega
  have square : dataWeight P fee + 1 ≤ (dataWeight P fee + 1) ^ 2 := by nlinarith
  exact linear.trans (Nat.mul_le_mul_left 4096 square)

theorem preFinal_resources (P : Parameters) (fee : ℚ) (trace : List State) (final : State)
    (preFinal : PreFinalState P fee final)
    (chain : trace.IsChain (fun a b => step program (rawInput P fee) a = some b))
    (last : trace.getLast? = some final) (length : trace.length ≤ lengthBudget P fee)
    (bounds : ∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) :
    time program trace ≤ 15 * lengthBudget P fee ∧ peakCells trace ≤ 84 ∧
      peakOperandBits trace ≤ operandBudget P fee + 21 := by
  have allEmpty := Prefix.outputs_empty program (rawInput P fee) trace final chain last preFinal.output
  have pcBound := (Prefix.chain_pc_cut program (rawInput P fee) (pc 45)
    (Prefix.terminal_step_forward (rawInput P fee)) trace final chain last preFinal.location).1
  refine ⟨(time_le_length program trace).trans (Nat.mul_le_mul_left 15 length), ?_, ?_⟩
  · apply peakCells_le_of_states trace 84
    intro state member
    have outputLength : state.output.length ≤ 13 := by rw [allEmpty state member]; decide
    exact workingCells_le_of_region state 64 13 (bounds state member).live outputLength
  · apply peakOperandBits_le_of_states
    intro state member
    have stateBound := bounds state member
    apply stateCellBits_le state 64 (pc 45) (operandBudget P fee + 21) stateBound.live (pcBound state member)
    · intro register
      have h := stateBound.registers register
      omega
    · intro address live
      have h := stateBound.heapValues address live
      omega
    · intro cell inOutput
      have h := stateBound.outputs cell inOutput
      omega
    · have small : natBits 64 = 7 := by decide
      omega
    · have small : natBits (pc 45) = 14 := by decide
      omega

end PDROC.D27Prepare.Assembly
