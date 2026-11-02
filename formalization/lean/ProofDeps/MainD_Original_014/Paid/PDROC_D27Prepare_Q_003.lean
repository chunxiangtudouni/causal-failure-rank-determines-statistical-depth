module

public import Paid.PDROC_D27Prepare_Q_002
public import Paid.PDROC_D27Prepare_Resources_007
public import Paid.PDROC_D27Prepare_Resources_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.DataBits

namespace PDROC.D27Prepare.Q

def firstValue (P : Parameters) : ℚ := ((P.certificate.M : ℚ) + 1) / P.certificate.gamma
def secondValue (P : Parameters) : ℚ := (2 * (P.certificate.E : ℚ)) / P.certificate.gamma ^ 2

theorem firstValue_nonnegative (P : Parameters) : 0 ≤ firstValue P :=
  div_nonneg (by positivity) P.certificate.gamma_pos.le

theorem secondValue_nonnegative (P : Parameters) : 0 ≤ secondValue P :=
  div_nonneg (by positivity) (sq_nonneg _)

theorem value_bits (P : Parameters) (fee : ℚ) :
    (Cell.rational (P.certificate.M : ℚ)).bits ≤ operandBudget P fee ∧
    (Cell.rational ((P.certificate.M : ℚ) + 1)).bits ≤ operandBudget P fee ∧
    (Cell.rational (firstValue P)).bits ≤ operandBudget P fee ∧
    (Cell.rational (P.certificate.E : ℚ)).bits ≤ operandBudget P fee ∧
    (Cell.rational (2 * (P.certificate.E : ℚ))).bits ≤ operandBudget P fee ∧
    (Cell.rational (secondValue P)).bits ≤ operandBudget P fee := by
  have data := scalar_data_bounds P fee
  have hM := data.2.2.1
  have hE := data.2.2.2.1
  have hg := data.2.2.2.2.2.2.1
  have hMe := natural_cast_encoding P fee P.certificate.M (by omega)
  have hEe := natural_cast_encoding P fee P.certificate.E (by omega)
  have hone : ratEncodingBits (1 : ℚ) = 3 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have htwo : ratEncodingBits (2 : ℚ) = 4 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hsum := ratEncodingBits_add_le (P.certificate.M : ℚ) (1 : ℚ)
  have hfirst := ratEncodingBits_div_le ((P.certificate.M : ℚ) + 1) P.certificate.gamma
  have hmul := ratEncodingBits_mul_le (2 : ℚ) (P.certificate.E : ℚ)
  have hg2 : ratEncodingBits (P.certificate.gamma ^ 2) ≤ 2 * dataWeight P fee := by
    have h := ratEncodingBits_mul_le P.certificate.gamma P.certificate.gamma
    rw [← pow_two] at h
    omega
  have hsecond := ratEncodingBits_div_le (2 * (P.certificate.E : ℚ)) (P.certificate.gamma ^ 2)
  have hb := linear_le_operandBudget P fee
  refine ⟨natural_cast_bits P fee _ (by omega), ?_, ?_, natural_cast_bits P fee _ (by omega), ?_, ?_⟩
  · exact le_trans (by change 1 + ratEncodingBits ((P.certificate.M : ℚ) + 1) ≤ 64 * (dataWeight P fee + 1); omega) hb
  · exact le_trans (by change 1 + ratEncodingBits (((P.certificate.M : ℚ) + 1) / P.certificate.gamma) ≤ 64 * (dataWeight P fee + 1); omega) hb
  · exact le_trans (by change 1 + ratEncodingBits (2 * (P.certificate.E : ℚ)) ≤ 64 * (dataWeight P fee + 1); omega) hb
  · exact le_trans (by change 1 + ratEncodingBits ((2 * (P.certificate.E : ℚ)) / P.certificate.gamma ^ 2) ≤ 64 * (dataWeight P fee + 1); omega) hb

def firstNext (memory : SlotMemory) (P : Parameters) : SlotMemory :=
  ((memory.write 32 (.rational P.certificate.M)).write 32
    (.rational ((P.certificate.M : ℚ) + 1))).write 32 (.rational (firstValue P))

def secondNext (memory : SlotMemory) (P : Parameters) : SlotMemory :=
  ((memory.write 32 (.rational P.certificate.E)).write 32
    (.rational (2 * (P.certificate.E : ℚ)))).write 32 (.rational (secondValue P))

theorem first_body_eval (memory : SlotMemory) (P : Parameters)
    (hM : Has memory 7 (.natural P.certificate.M)) (hone : Has memory 17 (.rational 1))
    (hgamma : Has memory 2 (.rational P.certificate.gamma)) :
    slotSequenceEval firstCeilSetupCommands memory = some (firstNext memory P) := by
  let m1 := memory.write 32 (.rational P.certificate.M)
  let m2 := m1.write 32 (.rational ((P.certificate.M : ℚ) + 1))
  have first := cast_eval memory 7 32 P.certificate.M hM
  have second := rational_eval m1 .add 32 17 32 (P.certificate.M : ℚ) 1
    ((P.certificate.M : ℚ) + 1) (Has.write_same _ _ _)
    (Has.write_other memory 17 32 (.rational 1) (.rational P.certificate.M) hone (by decide)) rfl
  have third := rational_eval m2 .divide 32 2 32 ((P.certificate.M : ℚ) + 1) P.certificate.gamma (firstValue P)
    (Has.write_same _ _ _) (by simpa [m2, m1, Has, SlotMemory.write] using hgamma)
    (by simp only [RatOp.eval, P.certificate.gamma_pos.ne', ↓reduceIte, firstValue])
  simp only [firstCeilSetupCommands, slotSequenceEval, first, Option.bind_some]
  change ((SlotCommand.rational .add 32 17 32).eval m1).bind
    (slotSequenceEval [.rational .divide 32 2 32]) = _
  rw [second, Option.bind_some]
  change ((SlotCommand.rational .divide 32 2 32).eval m2).bind (slotSequenceEval []) = _
  simp only [third, Option.bind_some, slotSequenceEval, firstNext, m2, m1]

theorem second_body_eval (memory : SlotMemory) (P : Parameters)
    (hE : Has memory 8 (.natural P.certificate.E)) (htwo : Has memory 18 (.rational 2))
    (hgammaSquared : Has memory 24 (.rational (P.certificate.gamma ^ 2))) :
    slotSequenceEval secondCeilSetupCommands memory = some (secondNext memory P) := by
  let m1 := memory.write 32 (.rational P.certificate.E)
  let m2 := m1.write 32 (.rational (2 * (P.certificate.E : ℚ)))
  have first := cast_eval memory 8 32 P.certificate.E hE
  have second := rational_eval m1 .multiply 18 32 32 2 (P.certificate.E : ℚ)
    (2 * (P.certificate.E : ℚ))
    (Has.write_other memory 18 32 (.rational 2) (.rational P.certificate.E) htwo (by decide))
    (Has.write_same _ _ _) rfl
  have third := rational_eval m2 .divide 32 24 32 (2 * (P.certificate.E : ℚ))
    (P.certificate.gamma ^ 2) (secondValue P) (Has.write_same _ _ _)
    (by simpa [m2, m1, Has, SlotMemory.write] using hgammaSquared)
    (by simp only [RatOp.eval, pow_ne_zero 2 P.certificate.gamma_pos.ne', ↓reduceIte, secondValue])
  simp only [secondCeilSetupCommands, slotSequenceEval, first, Option.bind_some]
  change ((SlotCommand.rational .multiply 18 32 32).eval m1).bind
    (slotSequenceEval [.rational .divide 32 24 32]) = _
  rw [second, Option.bind_some]
  change ((SlotCommand.rational .divide 32 24 32).eval m2).bind (slotSequenceEval []) = _
  simp only [third, Option.bind_some, slotSequenceEval, secondNext, m2, m1]

theorem first_body_memory_bounds (memory : SlotMemory) (P : Parameters) (fee : ℚ)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (hM : Has memory 7 (.natural P.certificate.M)) (hone : Has memory 17 (.rational 1))
    (hgamma : Has memory 2 (.rational P.certificate.gamma)) :
    SequenceMemoryBounds firstCeilSetupCommands memory 64 (operandBudget P fee) := by
  let m1 := memory.write 32 (.rational P.certificate.M)
  let m2 := m1.write 32 (.rational ((P.certificate.M : ℚ) + 1))
  let m3 := m2.write 32 (.rational (firstValue P))
  have bits := value_bits P fee
  have b1 : MemoryBounds 64 (operandBudget P fee) m1 := bounded.write 32 _ (by decide) bits.1
  have b2 : MemoryBounds 64 (operandBudget P fee) m2 := b1.write 32 _ (by decide) bits.2.1
  have b3 : MemoryBounds 64 (operandBudget P fee) m3 := b2.write 32 _ (by decide) bits.2.2.1
  have e1 := cast_eval memory 7 32 P.certificate.M hM
  have e2 := rational_eval m1 .add 32 17 32 (P.certificate.M : ℚ) 1 ((P.certificate.M : ℚ) + 1)
    (Has.write_same _ _ _) (by simpa [m1, Has, SlotMemory.write] using hone) rfl
  have e3 := rational_eval m2 .divide 32 2 32 ((P.certificate.M : ℚ) + 1) P.certificate.gamma (firstValue P)
    (Has.write_same _ _ _) (by simpa [m2, m1, Has, SlotMemory.write] using hgamma)
    (by simp only [RatOp.eval, P.certificate.gamma_pos.ne', ↓reduceIte, firstValue])
  exact SequenceMemoryBounds.cons _ _ memory m1 64 _ bounded e1
    (SequenceMemoryBounds.cons _ _ m1 m2 64 _ b1 e2
      (SequenceMemoryBounds.cons _ [] m2 m3 64 _ b2 e3 (SequenceMemoryBounds.nil m3 64 _ b3)))

theorem second_body_memory_bounds (memory : SlotMemory) (P : Parameters) (fee : ℚ)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (hE : Has memory 8 (.natural P.certificate.E)) (htwo : Has memory 18 (.rational 2))
    (hgammaSquared : Has memory 24 (.rational (P.certificate.gamma ^ 2))) :
    SequenceMemoryBounds secondCeilSetupCommands memory 64 (operandBudget P fee) := by
  let m1 := memory.write 32 (.rational P.certificate.E)
  let m2 := m1.write 32 (.rational (2 * (P.certificate.E : ℚ)))
  let m3 := m2.write 32 (.rational (secondValue P))
  have bits := value_bits P fee
  have b1 : MemoryBounds 64 (operandBudget P fee) m1 := bounded.write 32 _ (by decide) bits.2.2.2.1
  have b2 : MemoryBounds 64 (operandBudget P fee) m2 := b1.write 32 _ (by decide) bits.2.2.2.2.1
  have b3 : MemoryBounds 64 (operandBudget P fee) m3 := b2.write 32 _ (by decide) bits.2.2.2.2.2
  have e1 := cast_eval memory 8 32 P.certificate.E hE
  have e2 := rational_eval m1 .multiply 18 32 32 2 (P.certificate.E : ℚ) (2 * (P.certificate.E : ℚ))
    (by simpa [m1, Has, SlotMemory.write] using htwo) (Has.write_same _ _ _) rfl
  have e3 := rational_eval m2 .divide 32 24 32 (2 * (P.certificate.E : ℚ)) (P.certificate.gamma ^ 2) (secondValue P)
    (Has.write_same _ _ _) (by simpa [m2, m1, Has, SlotMemory.write] using hgammaSquared)
    (by simp only [RatOp.eval, pow_ne_zero 2 P.certificate.gamma_pos.ne', ↓reduceIte, secondValue])
  exact SequenceMemoryBounds.cons _ _ memory m1 64 _ bounded e1
    (SequenceMemoryBounds.cons _ _ m1 m2 64 _ b1 e2
      (SequenceMemoryBounds.cons _ [] m2 m3 64 _ b2 e3 (SequenceMemoryBounds.nil m3 64 _ b3)))

end PDROC.D27Prepare.Q
