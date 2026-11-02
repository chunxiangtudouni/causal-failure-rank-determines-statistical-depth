module

public import Paid.PDROC_D27Prepare_EndpointRun_002
public import Paid.PDROC_D27Prepare_Resources_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.EndpointRun

theorem setup_semantic_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (t0 : Has memory 6 (.natural P.certificate.t0))
    (ratN : Has memory 22 (.rational P.certificate.stages))
    (gamma : Has memory 2 (.rational P.certificate.gamma))
    (risk : Has memory 3 (.rational P.certificate.risk))
    (one : Has memory 17 (.rational 1)) (two : Has memory 18 (.rational 2))
    (four : Has memory 20 (.rational 4)) :
    SequenceMemoryBounds endpointSetupCommands memory 64 (operandBudget P fee) := by
  let D := P.certificate
  let m1 := memory.write 23 (.rational D.t0)
  let m2 := m1.write 32 (.rational (4 * (D.stages : ℚ)))
  let m3 := m2.write 32 (.rational (4 * (D.stages : ℚ) * D.t0))
  let m4 := m3.write 29 (.rational D.menuRatio)
  let m5 := m4.write 32 (.rational (2 * D.gamma))
  let m6 := m5.write 33 (.rational (1 + 2 * D.gamma))
  let m7 := m6.write 34 (.rational (1 - 2 * D.gamma))
  let m8 := m7.write 30 (.rational D.odds)
  let m9 := m8.write 28 (.rational 1)
  have e1 := cast_eval memory 6 23 D.t0 t0
  have e2 := rational_eval m1 .multiply 20 22 32 4 (D.stages : ℚ) (4 * (D.stages : ℚ))
    (by simpa [m1, Has, SlotMemory.write] using four)
    (by simpa [m1, Has, SlotMemory.write] using ratN) rfl
  have e3 := rational_eval m2 .multiply 32 23 32 (4 * (D.stages : ℚ)) (D.t0 : ℚ)
    (4 * (D.stages : ℚ) * D.t0) (Has.write_same _ _ _)
    (by simp [m2, m1, Has, SlotMemory.write]) rfl
  have hn : (D.stages : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt D.stages_pos)
  have ht : (D.t0 : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt D.t0_pos)
  have denominator : (4 : ℚ) * D.stages * D.t0 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hn) ht
  have e4 := rational_eval m3 .divide 3 32 29 D.risk (4 * (D.stages : ℚ) * D.t0) D.menuRatio
    (by simpa [m3, m2, m1, Has, SlotMemory.write] using risk) (Has.write_same _ _ _)
    (by simp only [RatOp.eval, denominator, ↓reduceIte, CertificateInput.menuRatio])
  have e5 := rational_eval m4 .multiply 18 2 32 2 D.gamma (2 * D.gamma)
    (by simpa [m4, m3, m2, m1, Has, SlotMemory.write] using two)
    (by simpa [m4, m3, m2, m1, Has, SlotMemory.write] using gamma) rfl
  have e6 := rational_eval m5 .add 17 32 33 1 (2 * D.gamma) (1 + 2 * D.gamma)
    (by simpa [m5, m4, m3, m2, m1, Has, SlotMemory.write] using one) (Has.write_same _ _ _) rfl
  have e7 := rational_eval m6 .subtract 17 32 34 1 (2 * D.gamma) (1 - 2 * D.gamma)
    (by simpa [m6, m5, m4, m3, m2, m1, Has, SlotMemory.write] using one)
    (by simp [m6, m5, Has, SlotMemory.write]) rfl
  have e8 := rational_eval m7 .divide 33 34 30 (1 + 2 * D.gamma) (1 - 2 * D.gamma) D.odds
    (by simp [m7, m6, Has, SlotMemory.write]) (Has.write_same _ _ _)
    (by simp only [RatOp.eval, D.denominator_pos.ne', ↓reduceIte, CertificateInput.odds])
  have e9 := copy_eval m8 17 28 (.rational 1)
    (by simpa [m8, m7, m6, m5, m4, m3, m2, m1, Has, SlotMemory.write] using one)
  have bits := setup_value_bits P fee
  have b1 : MemoryBounds 64 (operandBudget P fee) m1 := bounded.write 23 _ (by decide) (bits _ (by simp [D]))
  have b2 : MemoryBounds 64 (operandBudget P fee) m2 := b1.write 32 _ (by decide) (bits _ (by simp [D]))
  have b3 : MemoryBounds 64 (operandBudget P fee) m3 := b2.write 32 _ (by decide) (bits _ (by simp [D]))
  have b4 : MemoryBounds 64 (operandBudget P fee) m4 := b3.write 29 _ (by decide) (bits _ (by simp [D]))
  have b5 : MemoryBounds 64 (operandBudget P fee) m5 := b4.write 32 _ (by decide) (bits _ (by simp [D]))
  have b6 : MemoryBounds 64 (operandBudget P fee) m6 := b5.write 33 _ (by decide) (bits _ (by simp [D]))
  have b7 : MemoryBounds 64 (operandBudget P fee) m7 := b6.write 34 _ (by decide) (bits _ (by simp [D]))
  have b8 : MemoryBounds 64 (operandBudget P fee) m8 := b7.write 30 _ (by decide) (bits _ (by simp [D]))
  have b9 : MemoryBounds 64 (operandBudget P fee) m9 := b8.write 28 _ (by decide) (bits _ (by simp))
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

end PDROC.D27Prepare.EndpointRun
