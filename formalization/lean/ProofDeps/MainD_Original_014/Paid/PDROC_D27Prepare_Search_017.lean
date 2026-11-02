module

public import Paid.PDROC_D27Prepare_Search_010
public import Paid.PDROC_D27Prepare_Search_016
public import Paid.PDROC_D27Prepare_Resources_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Search

theorem majority_setup_semantic_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (stages : Has memory 0 (.natural P.certificate.stages))
    (gamma : Has memory 2 (.rational P.certificate.gamma))
    (risk : Has memory 3 (.rational P.certificate.risk))
    (one : Has memory 17 (.rational 1)) (two : Has memory 18 (.rational 2))
    (four : Has memory 20 (.rational 4)) :
    SequenceMemoryBounds majoritySetupCommands memory 64 (operandBudget P fee) := by
  let D := P.certificate
  let m1 := memory.write 22 (.rational D.stages)
  let m2 := m1.write 24 (.rational (D.gamma ^ 2))
  let m3 := m2.write 32 (.rational (4 * D.gamma ^ 2))
  let m4 := m3.write 25 (.rational D.varianceBase)
  let m5 := m4.write 26 (.rational (D.varianceBase ^ 2))
  let m6 := m5.write 32 (.rational (2 * (D.stages : ℚ)))
  let m7 := m6.write 33 (.rational (D.risk / (2 * (D.stages : ℚ))))
  let m8 := m7.write 27 (.rational ((D.risk / (2 * (D.stages : ℚ))) ^ 2))
  let m9 := m8.write 28 (.rational D.varianceBase)
  have e1 := cast_eval memory 0 22 D.stages stages
  have e2 := rational_eval m1 .multiply 2 2 24 D.gamma D.gamma (D.gamma ^ 2)
    (by simpa [m1, Has, SlotMemory.write] using gamma)
    (by simpa [m1, Has, SlotMemory.write] using gamma)
    (by simp [RatOp.eval, pow_two])
  have e3 := rational_eval m2 .multiply 20 24 32 4 (D.gamma ^ 2) (4 * D.gamma ^ 2)
    (by simpa [m2, m1, Has, SlotMemory.write] using four) (Has.write_same _ _ _) rfl
  have e4 := rational_eval m3 .subtract 17 32 25 1 (4 * D.gamma ^ 2) D.varianceBase
    (by simpa [m3, m2, m1, Has, SlotMemory.write] using one) (Has.write_same _ _ _)
    (by simp [RatOp.eval, CertificateInput.varianceBase])
  have var5 : Has m5 25 (.rational D.varianceBase) := by simp [m5, m4, Has, SlotMemory.write]
  have e5 := rational_eval m4 .multiply 25 25 26 D.varianceBase D.varianceBase (D.varianceBase ^ 2)
    (Has.write_same _ _ _) (Has.write_same _ _ _) (by simp [RatOp.eval, pow_two])
  have e6 := rational_eval m5 .multiply 18 22 32 2 (D.stages : ℚ) (2 * (D.stages : ℚ))
    (by simpa [m5, m4, m3, m2, m1, Has, SlotMemory.write] using two)
    (by simp [m5, m4, m3, m2, m1, Has, SlotMemory.write]) rfl
  have denominator : (2 : ℚ) * D.stages ≠ 0 := mul_ne_zero (by norm_num)
    (by exact_mod_cast (Nat.ne_of_gt D.stages_pos))
  have e7 := rational_eval m6 .divide 3 32 33 D.risk (2 * (D.stages : ℚ))
    (D.risk / (2 * (D.stages : ℚ)))
    (by simpa [m6, m5, m4, m3, m2, m1, Has, SlotMemory.write] using risk)
    (Has.write_same _ _ _) (by simp only [RatOp.eval, denominator, ↓reduceIte])
  have e8 := rational_eval m7 .multiply 33 33 27 (D.risk / (2 * (D.stages : ℚ)))
    (D.risk / (2 * (D.stages : ℚ))) ((D.risk / (2 * (D.stages : ℚ))) ^ 2)
    (Has.write_same _ _ _) (Has.write_same _ _ _) (by simp [RatOp.eval, pow_two])
  have var8 : Has m8 25 (.rational D.varianceBase) := by
    simpa [m8, m7, m6, Has, SlotMemory.write] using var5
  have e9 := copy_eval m8 25 28 (.rational D.varianceBase) var8
  have bits := majority_setup_value_bits P fee
  have b1 : MemoryBounds 64 (operandBudget P fee) m1 := bounded.write 22 _ (by decide) (bits _ (by simp [D]))
  have b2 : MemoryBounds 64 (operandBudget P fee) m2 := b1.write 24 _ (by decide) (bits _ (by simp [D]))
  have b3 : MemoryBounds 64 (operandBudget P fee) m3 := b2.write 32 _ (by decide) (bits _ (by simp [D]))
  have b4 : MemoryBounds 64 (operandBudget P fee) m4 := b3.write 25 _ (by decide) (bits _ (by simp [D]))
  have b5 : MemoryBounds 64 (operandBudget P fee) m5 := b4.write 26 _ (by decide) (bits _ (by simp [D]))
  have b6 : MemoryBounds 64 (operandBudget P fee) m6 := b5.write 32 _ (by decide) (bits _ (by simp [D]))
  have b7 : MemoryBounds 64 (operandBudget P fee) m7 := b6.write 33 _ (by decide) (bits _ (by simp [D]))
  have b8 : MemoryBounds 64 (operandBudget P fee) m8 := b7.write 27 _ (by decide) (bits _ (by simp [D]))
  have b9 : MemoryBounds 64 (operandBudget P fee) m9 := b8.write 28 _ (by decide) (bits _ (by simp [D]))
  exact SequenceMemoryBounds.cons _ _ memory m1 64 _ bounded e1
    (SequenceMemoryBounds.cons _ _ m1 m2 64 _ b1 e2
      (SequenceMemoryBounds.cons _ _ m2 m3 64 _ b2 e3
        (SequenceMemoryBounds.cons _ _ m3 m4 64 _ b3 e4
          (SequenceMemoryBounds.cons _ _ m4 m5 64 _ b4 e5
            (SequenceMemoryBounds.cons _ _ m5 m6 64 _ b5 e6
              (SequenceMemoryBounds.cons _ _ m6 m7 64 _ b6 e7
                (SequenceMemoryBounds.cons _ _ m7 m8 64 _ b7 e8
                  (SequenceMemoryBounds.cons _ [] m8 m9 64 _ b8 e9
                    (SequenceMemoryBounds.nil m9 64 _ b9)))))))))

end PDROC.D27Prepare.Search
