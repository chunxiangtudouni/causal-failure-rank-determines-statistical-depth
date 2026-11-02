module

public import Paid.PDROC_D27Prepare_Resources_007
public import Paid.PDROC_D27Prepare_Resources_010
public import Paid.PDROC_D27Prepare_Tail_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory

namespace PDROC.D27Prepare.Resources

theorem binomial_body_memory_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory) (i : ℕ)
    (index : i ≤ P.certificate.stages) (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (hN : Has memory 0 (.natural P.certificate.stages)) (hi : Has memory 40 (.natural i))
    (hone : Has memory 14 (.natural 1))
    (hchoose : Has memory 41 (.rational (P.certificate.stages.choose i))) :
    SequenceMemoryBounds binomialStepCommands memory 64 (operandBudget P fee) := by
  let N := P.certificate.stages
  let B := operandBudget P fee
  let m1 := memory.write 48 (.natural (N - i))
  let m2 := m1.write 49 (.natural (i + 1))
  let m3 := m2.write 32 (.rational (N - i : ℕ))
  let m4 := m3.write 33 (.rational (i + 1 : ℕ))
  let ratio : ℚ := ((N - i : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ)
  let m5 := m4.write 50 (.rational ratio)
  let m6 := m5.write 41 (.rational (N.choose (i + 1)))
  let m7 := m6.write 40 (.natural (i + 1))
  have hsize := (scalar_data_bounds P fee).1
  have b1 : MemoryBounds 64 B m1 := bounded.write 48 _ (by decide)
    (natural_small_bits P fee _ (by dsimp [N]; omega))
  have b2 : MemoryBounds 64 B m2 := b1.write 49 _ (by decide)
    (natural_small_bits P fee _ (by omega))
  have b3 : MemoryBounds 64 B m3 := b2.write 32 _ (by decide)
    (natural_cast_bits P fee _ (by dsimp [N]; omega))
  have b4 : MemoryBounds 64 B m4 := b3.write 33 _ (by decide)
    (natural_cast_bits P fee _ (by omega))
  have b5 : MemoryBounds 64 B m5 := b4.write 50 _ (by decide) (binomial_ratio_bits P fee i index)
  have b6 : MemoryBounds 64 B m6 := b5.write 41 _ (by decide) (binomial_choose_bits P fee (i + 1))
  have b7 : MemoryBounds 64 B m7 := b6.write 40 _ (by decide)
    (natural_small_bits P fee _ (by omega))
  have e1 : (SlotCommand.natural .subtract 0 40 48).eval memory = some m1 :=
    natural_eval memory .subtract 0 40 48 N i (N - i) hN hi rfl
  have e2 : (SlotCommand.natural .add 40 14 49).eval m1 = some m2 :=
    natural_eval m1 .add 40 14 49 i 1 (i + 1)
      (by simpa [m1, Has, SlotMemory.write] using hi)
      (by simpa [m1, Has, SlotMemory.write] using hone) rfl
  have e3 : (SlotCommand.toRational 48 32).eval m2 = some m3 :=
    cast_eval m2 48 32 (N - i) (by simp [m2, m1, Has, SlotMemory.write])
  have e4 : (SlotCommand.toRational 49 33).eval m3 = some m4 :=
    cast_eval m3 49 33 (i + 1) (by simp [m3, m2, Has, SlotMemory.write])
  have e5 : (SlotCommand.rational .divide 32 33 50).eval m4 = some m5 := by
    apply rational_eval m4 .divide 32 33 50 ((N - i : ℕ) : ℚ) ((i + 1 : ℕ) : ℚ) ratio
    · simp [m4, m3, Has, SlotMemory.write]
    · simp [m4, Has, SlotMemory.write]
    · have nonzero : ((i + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      simp only [RatOp.eval, nonzero, ↓reduceIte, ratio]
  have e6 : (SlotCommand.rational .multiply 41 50 41).eval m5 = some m6 := by
    apply rational_eval m5 .multiply 41 50 41 (N.choose i : ℚ) ratio (N.choose (i + 1) : ℚ)
    · simpa [m5, m4, m3, m2, m1, Has, SlotMemory.write, N] using hchoose
    · simp [m5, Has, SlotMemory.write]
    · simp only [RatOp.eval, ratio, PDROC.D27Prepare.Binomial.choose_rat_step_grouped]
  have e7 : (SlotCommand.copy 49 40).eval m6 = some m7 :=
    copy_eval m6 49 40 (.natural (i + 1)) (by simp [m6, m5, m4, m3, m2, Has, SlotMemory.write])
  unfold binomialStepCommands
  exact SequenceMemoryBounds.cons _ _ memory m1 64 B bounded e1
    (SequenceMemoryBounds.cons _ _ m1 m2 64 B b1 e2
      (SequenceMemoryBounds.cons _ _ m2 m3 64 B b2 e3
        (SequenceMemoryBounds.cons _ _ m3 m4 64 B b3 e4
          (SequenceMemoryBounds.cons _ _ m4 m5 64 B b4 e5
            (SequenceMemoryBounds.cons _ _ m5 m6 64 B b5 e6
              (SequenceMemoryBounds.cons _ _ m6 m7 64 B b6 e7
                (SequenceMemoryBounds.nil m7 64 B b7)))))))

theorem binomial_body_prefix_bounds (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (i : ℕ) (index : i ≤ P.certificate.stages)
    (matched : MemoryMatch before memory) (stateBound : StateBounds 64 (operandBudget P fee) before)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (hN : Has memory 0 (.natural P.certificate.stages)) (hi : Has memory 40 (.natural i))
    (hone : Has memory 14 (.natural 1))
    (hchoose : Has memory 41 (.rational (P.certificate.stages.choose i))) :
    LinearPrefixBounds input binomialStep before 64 (operandBudget P fee) := by
  apply slotSequence_prefix_bounds binomialStepCommands input before memory
    (PDROC.D27Prepare.Tail.binomialNext memory P.certificate.stages i) 64 (operandBudget P fee)
    matched stateBound _ (operandBudget_address_bits P fee)
    (PDROC.D27Prepare.Tail.binomial_body_eval memory P.certificate.stages i hN hi hone hchoose)
    (binomial_body_memory_bounds P fee memory i index bounded hN hi hone hchoose)
  intro command member
  simp only [binomialStepCommands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [CommandAddresses]

theorem tail_add_memory_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory) (K i : ℕ)
    (index : i ≤ P.certificate.stages) (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (htail : Has memory 42 (.rational (PDROC.D27Prepare.Binomial.partialTail P.certificate.stages K i)))
    (hchoose : Has memory 41 (.rational (P.certificate.stages.choose i))) :
    SequenceMemoryBounds PDROC.D27Prepare.Tail.tailAddCommands memory 64 (operandBudget P fee) := by
  let value : ℚ := (PDROC.D27Prepare.Binomial.partialTail P.certificate.stages K i : ℚ) +
    (P.certificate.stages.choose i : ℚ)
  let next := memory.write 42 (.rational value)
  have bits := binomial_tail_add_bits P fee
    (PDROC.D27Prepare.Binomial.partialTail P.certificate.stages K i) i
    (PDROC.D27Prepare.Binomial.partialTail_le _ _ _ (by omega))
  have nextBound : MemoryBounds 64 (operandBudget P fee) next := bounded.write 42 _ (by decide) bits
  have eval : (SlotCommand.rational .add 42 41 42).eval memory = some next :=
    rational_eval memory .add 42 41 42 _ _ value htail hchoose rfl
  exact SequenceMemoryBounds.cons _ [] memory next 64 (operandBudget P fee) bounded eval
    (SequenceMemoryBounds.nil next 64 (operandBudget P fee) nextBound)

theorem tail_add_prefix_bounds (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (K i : ℕ) (index : i ≤ P.certificate.stages)
    (matched : MemoryMatch before memory) (stateBound : StateBounds 64 (operandBudget P fee) before)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (htail : Has memory 42 (.rational (PDROC.D27Prepare.Binomial.partialTail P.certificate.stages K i)))
    (hchoose : Has memory 41 (.rational (P.certificate.stages.choose i))) :
    LinearPrefixBounds input (PDCompute.Solver.ratBinarySlots .add 42 41 42) before 64 (operandBudget P fee) := by
  apply slotSequence_prefix_bounds PDROC.D27Prepare.Tail.tailAddCommands input before memory
    (memory.write 42 (.rational ((PDROC.D27Prepare.Binomial.partialTail P.certificate.stages K i : ℚ) +
      (P.certificate.stages.choose i : ℚ)))) 64 (operandBudget P fee)
    matched stateBound _ (operandBudget_address_bits P fee)
    (PDROC.D27Prepare.Tail.tail_add_eval memory P.certificate.stages K i htail hchoose)
    (tail_add_memory_bounds P fee memory K i index bounded htail hchoose)
  intro command member
  have same : command = SlotCommand.rational .add 42 41 42 := List.mem_singleton.mp member
  subst command
  norm_num [CommandAddresses]

end PDROC.D27Prepare.Resources
