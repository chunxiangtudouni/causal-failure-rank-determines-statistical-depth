module

public import Paid.PDROC_BitVM_VM_CFG_Complete_002
public import Paid.PDROC_BitVM_VM_Phases_PolynomialOriginal_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.SourceBudget

open PaperProofs.Paid.Computation
open _root_.PDROC.BitVM.VM.Phases.Polynomial

/-- Pure upper clock of an already selected actual source trace. -/
def envelopeCost (coefficient degree envelope : ℕ) : ℕ :=
  (envelope + 1) * coefficient *
    (2 * BoundaryBudget.boundaryBudget envelope envelope envelope + 1)^degree + 1

theorem totalBudget_le (coefficient degree envelope : ℕ) (code : Program) (input : List Cell)
    (states : List State) (timeBound : time code states ≤ envelope)
    (bitsBound : peakOperandBits states ≤ envelope) (inputBound : (encodeBits input).length ≤ envelope) :
    CFG.Complete.totalBudget coefficient degree code input states + 1 ≤ envelopeCost coefficient degree envelope := by
  have boundary : CFG.Complete.envelope code input states ≤
      BoundaryBudget.boundaryBudget envelope envelope envelope := by
    unfold CFG.Complete.envelope BoundaryBudget.boundaryBudget
    exact Nat.mul_le_mul_left 128 (Nat.add_le_add_right
      (Nat.add_le_add inputBound (Nat.mul_le_mul (Nat.succ_le_succ timeBound) (Nat.succ_le_succ bitsBound))) 1)
  exact Nat.add_le_add_right
    (Nat.mul_le_mul (Nat.mul_le_mul_right coefficient (Nat.succ_le_succ timeBound))
      (Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.mul_le_mul_left 2 boundary)) degree)) 1

theorem envelopeCost_scalar {E : ℕ → ℕ} (bounded : ScalarBound E) (coefficient degree : ℕ) :
    ScalarBound (fun S => envelopeCost coefficient degree (E S)) := by
  have one := ScalarBound.constant 1
  have next := bounded.add one
  have boundary : ScalarBound (fun S => BoundaryBudget.boundaryBudget (E S) (E S) (E S)) := by
    simpa only [BoundaryBudget.boundaryBudget] using
      (ScalarBound.constant 128).mul ((bounded.add (next.mul next)).add one)
  simpa only [envelopeCost] using
    (((next.mul (ScalarBound.constant coefficient)).mul
      ((((ScalarBound.constant 2).mul boundary).add one).power degree)).add one)

end PDROC.BitVM.VM.Phases.SourceBudget
