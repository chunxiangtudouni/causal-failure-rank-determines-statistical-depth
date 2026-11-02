module

public import Paid.PDROC_D27Prepare_Memory_001
public import Paid.PDROC_D27Prepare_Binomial_001
public import Paid.PDROC_D27Prepare_Budget_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.D27Prepare.Tail

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open Program Memory

/-- The exact writes of page21 before its jump to the dyadic guard. -/
def multiplierNext (memory : SlotMemory) (P : Parameters) : SlotMemory :=
  (((((memory.write 32 (.rational (4 * P.reviewFee))).write 32
    (.rational (4 * P.reviewFee * P.certificate.stages))).write 32
    (.rational (4 * P.reviewFee * P.certificate.stages * P.certificate.t0))).write
    11 (.rational P.Lambda)).write 35 (.natural 0)).write 39 (.rational 1)

theorem multiplier_body_eval (memory : SlotMemory) (P : Parameters)
    (hfour : Has memory 20 (.rational 4))
    (hfee : Has memory 4 (.rational P.reviewFee))
    (hN : Has memory 22 (.rational P.certificate.stages))
    (ht : Has memory 23 (.rational P.certificate.t0))
    (hrisk : Has memory 3 (.rational P.certificate.risk))
    (hzero : Has memory 13 (.natural 0)) (hone : Has memory 17 (.rational 1)) :
    slotSequenceEval multiplierSetupCommands memory = some (multiplierNext memory P) := by
  have numerator : 4 * P.reviewFee * (P.certificate.stages : ℚ) * P.certificate.t0 = 4 * P.B := by
    unfold B
    ring
  simp [slotSequenceEval, multiplierSetupCommands, SlotCommand.eval, SlotMemory.write,
    hfour.1, hfour.2, hfee.1, hfee.2, hN.1, hN.2, ht.1, ht.2, hrisk.1, hrisk.2,
    hzero.1, hzero.2, hone.1, hone.2, Cell.rat?, RatOp.eval,
    P.certificate.risk_pos.ne', multiplierNext, Lambda, numerator]

/-- Exact physical writes of the actual dyadic update body. -/
def dyadicNext (memory : SlotMemory) (i : ℕ) : SlotMemory :=
  (memory.write 35 (.natural (i + 1))).write 39 (.rational ((1 / 2 : ℚ) ^ (i + 1)))

theorem dyadic_body_eval (memory : SlotMemory) (i : ℕ)
    (hindex : Has memory 35 (.natural i)) (hone : Has memory 14 (.natural 1))
    (hpower : Has memory 39 (.rational ((1 / 2 : ℚ) ^ i)))
    (hhalf : Has memory 21 (.rational (1 / 2))) :
    slotSequenceEval dyadicStepCommands memory = some (dyadicNext memory i) := by
  have first := natural_eval memory .add 35 14 35 i 1 (i + 1) hindex hone rfl
  have hp := Has.write_other memory 39 35 (.rational ((1 / 2 : ℚ) ^ i))
    (.natural (i + 1)) hpower (by decide)
  have hh := Has.write_other memory 21 35 (.rational (1 / 2))
    (.natural (i + 1)) hhalf (by decide)
  have second := rational_eval (memory.write 35 (.natural (i + 1))) .multiply 39 21 39
    ((1 / 2 : ℚ) ^ i) (1 / 2) ((1 / 2 : ℚ) ^ (i + 1)) hp hh
    (by simp only [RatOp.eval, Binomial.dyadic_step])
  simp only [dyadicStepCommands, slotSequenceEval, first, Option.bind_some, second, dyadicNext]

/-- Exact writes at page44. The halving takes one division by the constant2,
regardless of the numeric size of the tiny-fee rational ceiling. -/
def halveNext (memory : SlotMemory) (x j : ℕ) : SlotMemory :=
  (memory.write 47 (.natural (x / 2))).write 10 (.natural (j + 1))

theorem halve_body_eval (memory : SlotMemory) (x j : ℕ)
    (hx : Has memory 47 (.natural x)) (hj : Has memory 10 (.natural j))
    (htwo : Has memory 15 (.natural 2)) (hone : Has memory 14 (.natural 1)) :
    slotSequenceEval budgetHalveStepCommands memory = some (halveNext memory x j) := by
  have first := natural_eval memory .divide 47 15 47 x 2 (x / 2) hx htwo
    (by simp [NatOp.eval])
  have hja := Has.write_other memory 10 47 (.natural j) (.natural (x / 2)) hj (by decide)
  have hoa := Has.write_other memory 14 47 (.natural 1) (.natural (x / 2)) hone (by decide)
  have second := natural_eval (memory.write 47 (.natural (x / 2))) .add 10 14 10 j 1 (j + 1) hja hoa rfl
  simp only [budgetHalveStepCommands, slotSequenceEval, first, Option.bind_some, second, halveNext]

def binomialInitial (memory : SlotMemory) : SlotMemory :=
  ((memory.write 40 (.natural 0)).write 41 (.rational 1)).write 42 (.rational 0)

theorem binomial_setup_eval (memory : SlotMemory)
    (hzero : Has memory 13 (.natural 0)) (hone : Has memory 17 (.rational 1))
    (hrzero : Has memory 16 (.rational 0)) :
    slotSequenceEval binomialSetupCommands memory = some (binomialInitial memory) := by
  simp [slotSequenceEval, binomialSetupCommands, SlotCommand.eval, SlotMemory.write,
    hzero.1, hzero.2, hone.1, hone.2, hrzero.1, hrzero.2, binomialInitial]

/-- All seven writes in page30, including the final i=N iteration.
No work is proportional to K. -/
def binomialNext (memory : SlotMemory) (N i : ℕ) : SlotMemory :=
  ((((((memory.write 48 (.natural (N - i))).write 49 (.natural (i + 1))).write
    32 (.rational (N - i : ℕ))).write 33 (.rational (i + 1 : ℕ))).write
    50 (.rational (((N - i : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ)))).write
    41 (.rational (N.choose (i + 1)))).write 40 (.natural (i + 1))

theorem binomial_body_eval (memory : SlotMemory) (N i : ℕ)
    (hN : Has memory 0 (.natural N)) (hi : Has memory 40 (.natural i))
    (hone : Has memory 14 (.natural 1))
    (hchoose : Has memory 41 (.rational (N.choose i))) :
    slotSequenceEval binomialStepCommands memory = some (binomialNext memory N i) := by
  have nonzero : (i : ℚ) + 1 ≠ 0 := by positivity
  have coefficient := Binomial.choose_rat_step_grouped N i
  simp only [Nat.cast_add, Nat.cast_one] at coefficient
  simp [slotSequenceEval, binomialStepCommands, SlotCommand.eval, SlotMemory.write,
    hN.1, hN.2, hi.1, hi.2, hone.1, hone.2, hchoose.1, hchoose.2,
    Cell.nat?, Cell.rat?, NatOp.eval, RatOp.eval, nonzero,
    coefficient, binomialNext]

theorem binomial_next_choose (memory : SlotMemory) (N i : ℕ) :
    Has (binomialNext memory N i) 41 (.rational (N.choose (i + 1))) := by
  apply Has.write_other
  · apply Has.write_same
  · decide

theorem binomial_next_index (memory : SlotMemory) (N i : ℕ) :
    Has (binomialNext memory N i) 40 (.natural (i + 1)) := Has.write_same _ _ _

def tailAddCommands : List SlotCommand := [.rational .add 42 41 42]

theorem tailAdd_compiled : slotSequenceCode tailAddCommands =
    PDCompute.Solver.ratBinarySlots .add 42 41 42 := rfl

theorem tail_add_eval (memory : SlotMemory) (N K i : ℕ)
    (htail : Has memory 42 (.rational (Binomial.partialTail N K i)))
    (hchoose : Has memory 41 (.rational (N.choose i))) :
    slotSequenceEval tailAddCommands memory = some (memory.write 42
      (.rational ((Binomial.partialTail N K i : ℚ) + (N.choose i : ℚ)))) := by
  simp only [tailAddCommands, slotSequenceEval,
    rational_eval memory .add 42 41 42 _ _ _ htail hchoose rfl, Option.bind_some]

def nonzeroZetaCommands : List SlotCommand := [.rational .subtract 17 39 12]

theorem nonzeroZeta_compiled : slotSequenceCode nonzeroZetaCommands ++ go 32 = pageCode 25 := rfl

theorem nonzero_zeta_eval (memory : SlotMemory) (P : Parameters) (fee : ℚ) (hne : fee ≠ 0)
    (hone : Has memory 17 (.rational 1))
    (hpower : Has memory 39 (.rational ((1 / 2 : ℚ) ^ P.certificate.stages))) :
    slotSequenceEval nonzeroZetaCommands memory =
      some (memory.write 12 (.rational (P.zeroChargeRisk fee))) := by
  have eval := rational_eval memory .subtract 17 39 12 1
    ((1 / 2 : ℚ) ^ P.certificate.stages)
    (1 - (1 / 2 : ℚ) ^ P.certificate.stages) hone hpower rfl
  simp only [nonzeroZetaCommands, slotSequenceEval, eval, Option.bind_some,
    zeroChargeRisk, hne, ↓reduceIte]

def zeroZetaCommands : List SlotCommand := [.rational .multiply 42 39 12]

theorem zeroZeta_compiled : slotSequenceCode zeroZetaCommands ++ go 32 = pageCode 31 := rfl

theorem zero_zeta_eval (memory : SlotMemory) (P : Parameters)
    (htail : Has memory 42 (.rational (Binomial.partialTail P.certificate.stages
      P.tools (P.certificate.stages + 1))))
    (hpower : Has memory 39 (.rational ((1 / 2 : ℚ) ^ P.certificate.stages))) :
    slotSequenceEval zeroZetaCommands memory =
      some (memory.write 12 (.rational (P.zeroChargeRisk 0))) := by
  have op : RatOp.multiply.eval
      (Binomial.partialTail P.certificate.stages P.tools (P.certificate.stages + 1))
      ((1 / 2 : ℚ) ^ P.certificate.stages) = some (P.zeroChargeRisk 0) := by
    simp only [RatOp.eval, Binomial.original_zeta_fee_zero]
  have eval := rational_eval memory .multiply 42 39 12 _ _ _ htail hpower op
  simp only [zeroZetaCommands, slotSequenceEval, eval, Option.bind_some]

theorem first_floor_zero_eval (memory : SlotMemory) (P : Parameters)
    (hc : Has memory 4 (.rational P.reviewFee)) :
    (SlotCommand.copy 4 43).eval memory =
      some (memory.write 43 (.rational (P.firstChargeFloor 0))) := by
  simpa [firstChargeFloor] using copy_eval memory 4 43 (.rational P.reviewFee) hc

theorem first_floor_review_eval (memory : SlotMemory) (P : Parameters) (fee : ℚ)
    (hne : fee ≠ 0) (hmin : P.reviewFee ≤ fee) (hc : Has memory 4 (.rational P.reviewFee)) :
    (SlotCommand.copy 4 43).eval memory =
      some (memory.write 43 (.rational (P.firstChargeFloor fee))) := by
  simpa [firstChargeFloor, hne, min_eq_left hmin] using
    copy_eval memory 4 43 (.rational P.reviewFee) hc

theorem first_floor_fee_eval (memory : SlotMemory) (P : Parameters) (fee : ℚ)
    (hne : fee ≠ 0) (hmin : fee ≤ P.reviewFee) (hf : Has memory 5 (.rational fee)) :
    (SlotCommand.copy 5 43).eval memory =
      some (memory.write 43 (.rational (P.firstChargeFloor fee))) := by
  simpa [firstChargeFloor, hne, min_eq_right hmin] using
    copy_eval memory 5 43 (.rational fee) hf

def positiveFloorCommands : List SlotCommand :=
  [.rational .subtract 12 3 32, .rational .multiply 43 32 44]

theorem positiveFloor_compiled : slotSequenceCode positiveFloorCommands ++
    ratCompareSlots .less 16 44 = positiveFloorSetup := rfl

def positiveFloorNext (memory : SlotMemory) (P : Parameters) (fee : ℚ) : SlotMemory :=
  (memory.write 32 (.rational (P.zeroChargeRisk fee - P.certificate.risk))).write
    44 (.rational (P.positiveValueFloor fee))

theorem positiveFloor_body_eval (memory : SlotMemory) (P : Parameters) (fee : ℚ)
    (hz : Has memory 12 (.rational (P.zeroChargeRisk fee)))
    (hr : Has memory 3 (.rational P.certificate.risk))
    (hf : Has memory 43 (.rational (P.firstChargeFloor fee))) :
    slotSequenceEval positiveFloorCommands memory = some (positiveFloorNext memory P fee) := by
  simp [slotSequenceEval, positiveFloorCommands, SlotCommand.eval, SlotMemory.write,
    hz.1, hz.2, hr.1, hr.2, hf.1, hf.2, Cell.rat?, RatOp.eval,
    positiveFloorNext, positiveValueFloor]

def ratioNext (memory : SlotMemory) (P : Parameters) (fee : ℚ) : SlotMemory :=
  ((memory.write 32 (.rational (2 * P.Lambda))).write 32
    (.rational (2 * P.Lambda * P.certificate.risk))).write
    45 (.rational (Budget.originalRatio P fee))

theorem ratio_body_eval (memory : SlotMemory) (P : Parameters) (fee : ℚ)
    (htwo : Has memory 18 (.rational 2)) (hL : Has memory 11 (.rational P.Lambda))
    (hr : Has memory 3 (.rational P.certificate.risk))
    (hf : Has memory 44 (.rational (P.positiveValueFloor fee)))
    (positive : 0 < P.positiveValueFloor fee) :
    slotSequenceEval budgetRatioSetupCommands memory = some (ratioNext memory P fee) := by
  simp [slotSequenceEval, budgetRatioSetupCommands, SlotCommand.eval, SlotMemory.write,
    htwo.1, htwo.2, hL.1, hL.2, hr.1, hr.2, hf.1, hf.2, Cell.rat?, RatOp.eval,
    positive.ne', ratioNext, Budget.originalRatio]

def halveInitial (memory : SlotMemory) (ceiling : ℕ) : SlotMemory :=
  (memory.write 47 (.natural (ceiling - 1))).write 10 (.natural 0)

theorem halve_setup_eval (memory : SlotMemory) (ceiling : ℕ)
    (hc : Has memory 46 (.natural ceiling)) (hone : Has memory 14 (.natural 1))
    (hzero : Has memory 13 (.natural 0)) :
    slotSequenceEval budgetHalveSetupCommands memory = some (halveInitial memory ceiling) := by
  simp [slotSequenceEval, budgetHalveSetupCommands, SlotCommand.eval, SlotMemory.write,
    hc.1, hc.2, hone.1, hone.2, hzero.1, hzero.2, Cell.nat?, NatOp.eval, halveInitial]

end PDROC.D27Prepare.Tail
