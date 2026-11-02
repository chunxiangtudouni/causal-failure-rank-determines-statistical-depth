module

public import Paid.PDROC_D27Prepare_Tail_001
public import Paid.PDROC_D27Prepare_Resources_010
public import Paid.PDROC_D27Prepare_Resources_007
public import Paid.PDROC_D27Prepare_J_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Tail PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.Dyadic

def region : Finset ℕ := {11, 32, 35, 39}

theorem multiplier_semantic_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (four : Has memory 20 (.rational 4)) (reviewFee : Has memory 4 (.rational P.reviewFee))
    (stages : Has memory 22 (.rational P.certificate.stages)) (t0 : Has memory 23 (.rational P.certificate.t0))
    (risk : Has memory 3 (.rational P.certificate.risk)) (zero : Has memory 13 (.natural 0))
    (one : Has memory 17 (.rational 1)) :
    SequenceMemoryBounds multiplierSetupCommands memory 64 (operandBudget P fee) := by
  let m1 := memory.write 32 (.rational (4 * P.reviewFee))
  let m2 := m1.write 32 (.rational (4 * P.reviewFee * P.certificate.stages))
  let m3 := m2.write 32 (.rational (4 * P.reviewFee * P.certificate.stages * P.certificate.t0))
  let m4 := m3.write 11 (.rational P.Lambda)
  let m5 := m4.write 35 (.natural 0)
  let m6 := m5.write 39 (.rational 1)
  have e1 := rational_eval memory .multiply 20 4 32 4 P.reviewFee (4 * P.reviewFee) four reviewFee rfl
  have e2 := rational_eval m1 .multiply 32 22 32 (4 * P.reviewFee) (P.certificate.stages : ℚ)
    (4 * P.reviewFee * P.certificate.stages) (Has.write_same _ _ _)
    (by simpa [m1, Has, SlotMemory.write] using stages) rfl
  have e3 := rational_eval m2 .multiply 32 23 32 (4 * P.reviewFee * P.certificate.stages) (P.certificate.t0 : ℚ)
    (4 * P.reviewFee * P.certificate.stages * P.certificate.t0) (Has.write_same _ _ _)
    (by simpa [m2, m1, Has, SlotMemory.write] using t0) rfl
  have numerator : 4 * P.reviewFee * (P.certificate.stages : ℚ) * P.certificate.t0 = 4 * P.B := by
    unfold B
    ring
  have e4 := rational_eval m3 .divide 32 3 11 (4 * P.reviewFee * P.certificate.stages * P.certificate.t0)
    P.certificate.risk P.Lambda (Has.write_same _ _ _)
    (by simpa [m3, m2, m1, Has, SlotMemory.write] using risk)
    (by simp only [RatOp.eval, P.certificate.risk_pos.ne', ↓reduceIte, numerator, Lambda])
  have e5 := copy_eval m4 13 35 (.natural 0)
    (by simpa [m4, m3, m2, m1, Has, SlotMemory.write] using zero)
  have e6 := copy_eval m5 17 39 (.rational 1)
    (by simpa [m5, m4, m3, m2, m1, Has, SlotMemory.write] using one)
  have bits := multiplier_intermediate_bits P fee
  have hL : ratEncodingBits P.Lambda ≤ dataWeight P fee := by unfold dataWeight; omega
  have oneBits : (Cell.rational 1).bits ≤ operandBudget P fee := by
    simpa only [one.2] using bounded.values 17 one.1
  have b1 := bounded.write 32 (.rational (4 * P.reviewFee)) (by decide) bits.1
  have b2 := b1.write 32 (.rational (4 * P.reviewFee * P.certificate.stages)) (by decide) bits.2.1
  have b3 := b2.write 32 (.rational (4 * P.reviewFee * P.certificate.stages * P.certificate.t0)) (by decide) bits.2.2
  have b4 : MemoryBounds 64 (operandBudget P fee) m4 := b3.write 11 (.rational P.Lambda) (by decide) (rational_data_bits P fee _ hL)
  have b5 : MemoryBounds 64 (operandBudget P fee) m5 := b4.write 35 (.natural 0) (by decide) (natural_small_bits P fee 0 (by omega))
  have b6 : MemoryBounds 64 (operandBudget P fee) m6 := b5.write 39 (.rational 1) (by decide) oneBits
  exact SequenceMemoryBounds.cons _ _ memory m1 64 _ bounded e1
    (SequenceMemoryBounds.cons _ _ m1 m2 64 _ b1 e2
      (SequenceMemoryBounds.cons _ _ m2 m3 64 _ b2 e3
        (SequenceMemoryBounds.cons _ _ m3 m4 64 _ b3 e4
          (SequenceMemoryBounds.cons _ _ m4 m5 64 _ b4 e5
            (SequenceMemoryBounds.cons _ [] m5 m6 64 _ b5 e6
              (SequenceMemoryBounds.nil m6 64 _ b6))))))

end PDROC.D27Prepare.Dyadic
