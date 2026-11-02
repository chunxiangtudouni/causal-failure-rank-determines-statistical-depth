module

public import Paid.PDROC_D27Prepare_J_001
public import Paid.PDROC_D27Prepare_Tail_001
public import Paid.PDROC_D27Prepare_Resources_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Tail

namespace PDROC.D27Prepare.J

theorem ratio_semantic_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (htwo : Has memory 18 (.rational 2)) (hL : Has memory 11 (.rational P.Lambda))
    (hr : Has memory 3 (.rational P.certificate.risk))
    (hf : Has memory 44 (.rational (P.positiveValueFloor fee)))
    (positive : 0 < P.positiveValueFloor fee) :
    SequenceMemoryBounds budgetRatioSetupCommands memory 64 (operandBudget P fee) := by
  let m1 := memory.write 32 (.rational (2 * P.Lambda))
  let m2 := m1.write 32 (.rational (2 * P.Lambda * P.certificate.risk))
  have first := rational_eval memory .multiply 18 11 32 2 P.Lambda (2 * P.Lambda) htwo hL rfl
  have second := rational_eval m1 .multiply 32 3 32 (2 * P.Lambda) P.certificate.risk
    (2 * P.Lambda * P.certificate.risk) (Has.write_same _ _ _)
    (by simpa [m1, Has, SlotMemory.write] using hr) rfl
  have third := rational_eval m2 .divide 32 44 45 (2 * P.Lambda * P.certificate.risk)
    (P.positiveValueFloor fee) (Budget.originalRatio P fee) (Has.write_same _ _ _)
    (by simpa [m2, m1, Has, SlotMemory.write] using hf)
    (by simp only [RatOp.eval, positive.ne', ↓reduceIte, Budget.originalRatio])
  have bits := ratio_intermediate_bits P fee
  have b1 := bounded.write 32 (.rational (2 * P.Lambda)) (by decide) bits.1
  have b2 := b1.write 32 (.rational (2 * P.Lambda * P.certificate.risk)) (by decide) bits.2
  have ratioEncoding : ratEncodingBits (Budget.originalRatio P fee) ≤ dataWeight P fee := by
    change ratEncodingBits (Resources.originalRatio P fee) ≤ dataWeight P fee
    unfold dataWeight
    omega
  have b3 : MemoryBounds 64 (operandBudget P fee) (ratioNext memory P fee) :=
    b2.write 45 (.rational (Budget.originalRatio P fee)) (by decide)
      (rational_data_bits P fee _ ratioEncoding)
  exact SequenceMemoryBounds.cons _ _ memory m1 64 _ bounded first
    (SequenceMemoryBounds.cons _ _ m1 m2 64 _ b1 second
      (SequenceMemoryBounds.cons _ [] m2 (ratioNext memory P fee) 64 _ b2 third
        (SequenceMemoryBounds.nil _ _ _ b3)))

theorem halve_setup_semantic_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (hc : Has memory 46 (.natural (Nat.ceil (Budget.originalRatio P fee))))
    (hone : Has memory 14 (.natural 1)) (hzero : Has memory 13 (.natural 0)) :
    SequenceMemoryBounds budgetHalveSetupCommands memory 64 (operandBudget P fee) := by
  let ceiling := Nat.ceil (Budget.originalRatio P fee)
  let middle := memory.write 47 (.natural (ceiling - 1))
  have first := natural_eval memory .subtract 46 14 47 ceiling 1 (ceiling - 1) hc hone rfl
  have nextZero : Has middle 13 (.natural 0) :=
    Has.write_other memory 13 47 _ _ hzero (by decide)
  have second := copy_eval middle 13 10 (.natural 0) nextZero
  have bits := budget_halving_bits P fee (ceiling - 1) 0 (Nat.sub_le _ _) (Nat.zero_le _)
  have b1 := bounded.write 47 (.natural (ceiling - 1)) (by decide) bits.1
  have b2 : MemoryBounds 64 (operandBudget P fee) (halveInitial memory ceiling) :=
    b1.write 10 (.natural 0) (by decide) (natural_small_bits P fee 0 (by omega))
  exact SequenceMemoryBounds.cons _ _ memory middle 64 _ bounded first
    (SequenceMemoryBounds.cons _ [] middle (halveInitial memory ceiling) 64 _ b1 second
      (SequenceMemoryBounds.nil _ _ _ b2))

end PDROC.D27Prepare.J
