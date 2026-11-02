module

public import Paid.PDROC_D27Prepare_Tail_001
public import Paid.PDROC_D27Prepare_Resources_006
public import Paid.PDROC_D27Prepare_Resources_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.D27Prepare.TailBounds

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open Program Memory Tail Resources

theorem memory_of_state (state : State) (memory : SlotMemory) (H B : ℕ)
    (matched : MemoryMatch state memory) (bounded : StateBounds H B state) :
    MemoryBounds H B memory := by
  constructor
  · simpa only [matched.live] using bounded.live
  · simpa only [matched.live, matched.heap] using bounded.heapValues

/-- Every semantic prefix has bounded physical values; the command
compiler turns this finite certificate into all real instruction prefixes. -/
theorem dyadic_semantic_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory) (i : ℕ)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (hi : i < P.certificate.stages)
    (hindex : Has memory 35 (.natural i)) (hone : Has memory 14 (.natural 1))
    (hpower : Has memory 39 (.rational ((1 / 2 : ℚ) ^ i)))
    (hhalf : Has memory 21 (.rational (1 / 2))) :
    SequenceMemoryBounds dyadicStepCommands memory 64 (operandBudget P fee) := by
  let middle := memory.write 35 (.natural (i + 1))
  have first : (SlotCommand.natural .add 35 14 35).eval memory = some middle :=
    natural_eval memory .add 35 14 35 i 1 (i + 1) hindex hone rfl
  have hN := (scalar_data_bounds P fee).1
  have middleBound : MemoryBounds 64 (operandBudget P fee) middle :=
    bounded.write 35 (.natural (i + 1)) (by decide)
      (natural_small_bits P fee (i + 1) (by omega))
  have hp := Has.write_other memory 39 35 (.rational ((1 / 2 : ℚ) ^ i))
    (.natural (i + 1)) hpower (by decide)
  have hh := Has.write_other memory 21 35 (.rational (1 / 2))
    (.natural (i + 1)) hhalf (by decide)
  have second : (SlotCommand.rational .multiply 39 21 39).eval middle =
      some (dyadicNext memory i) :=
    rational_eval middle .multiply 39 21 39 _ _ _ hp hh
      (by simp only [RatOp.eval, Binomial.dyadic_step])
  have finalBound : MemoryBounds 64 (operandBudget P fee) (dyadicNext memory i) :=
    middleBound.write 39 (.rational ((1 / 2 : ℚ) ^ (i + 1))) (by decide)
      (dyadic_intermediate_bits P fee (i + 1) (by omega))
  exact SequenceMemoryBounds.cons _ _ _ middle _ _ bounded first
    (SequenceMemoryBounds.cons _ [] middle (dyadicNext memory i) _ _ middleBound second
      (SequenceMemoryBounds.nil _ _ _ finalBound))

theorem halve_semantic_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory) (x j : ℕ)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (hx : x ≤ ⌈Budget.originalRatio P fee⌉₊) (hj : j ≤ P.bisectionBudget fee)
    (hvalue : Has memory 47 (.natural x)) (hcounter : Has memory 10 (.natural j))
    (htwo : Has memory 15 (.natural 2)) (hone : Has memory 14 (.natural 1)) :
    SequenceMemoryBounds budgetHalveStepCommands memory 64 (operandBudget P fee) := by
  let middle := memory.write 47 (.natural (x / 2))
  have first : (SlotCommand.natural .divide 47 15 47).eval memory = some middle :=
    natural_eval memory .divide 47 15 47 x 2 (x / 2) hvalue htwo (by simp [NatOp.eval])
  have bits := budget_halving_bits P fee x j hx hj
  have middleBound : MemoryBounds 64 (operandBudget P fee) middle :=
    bounded.write 47 (.natural (x / 2)) (by decide) bits.2.1
  have hja := Has.write_other memory 10 47 (.natural j) (.natural (x / 2)) hcounter (by decide)
  have hoa := Has.write_other memory 14 47 (.natural 1) (.natural (x / 2)) hone (by decide)
  have second : (SlotCommand.natural .add 10 14 10).eval middle = some (halveNext memory x j) :=
    natural_eval middle .add 10 14 10 j 1 (j + 1) hja hoa rfl
  have finalBound : MemoryBounds 64 (operandBudget P fee) (halveNext memory x j) :=
    middleBound.write 10 (.natural (j + 1)) (by decide) bits.2.2
  exact SequenceMemoryBounds.cons _ _ _ middle _ _ bounded first
    (SequenceMemoryBounds.cons _ [] middle (halveNext memory x j) _ _ middleBound second
      (SequenceMemoryBounds.nil _ _ _ finalBound))

theorem address_bits (P : Parameters) (fee : ℚ) : 1 + natBits 64 ≤ operandBudget P fee := by
  have h := linear_le_operandBudget P fee
  have : 8 ≤ 64 * (dataWeight P fee + 1) := by omega
  simpa only [natBits, show Nat.log2 64 = 6 by decide] using this.trans h

end PDROC.D27Prepare.TailBounds
