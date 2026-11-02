module

public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.D27Prepare

open PaperProofs.Paid PaperProofs.Paid.Computation

/-- Exactly the preparation field of the original uniform rational ISA
claim, separated so that one fixed program can be consumed by the other
independent solver/calibration/core components. The input is the original
six cells, with no derived certificate or successful-run data. -/
def ExactPrepareClaims : Prop :=
  ∃ (prepare : Program) (Cprepare degree : ℕ), 0 < Cprepare ∧
    ∀ (P : Parameters) (fee : ℚ), 0 ≤ fee →
      ∃ trace final, Runs prepare (rawInput P fee) trace final ∧
        final.output = preparedInput P fee ∧
        time prepare trace ≤ Cprepare * (variableGammaSize P fee)^degree ∧
        peakCells trace ≤ Cprepare * (variableGammaSize P fee)^degree ∧
        peakOperandBits trace ≤ Cprepare * (variableGammaSize P fee)^degree

end PDROC.D27Prepare
