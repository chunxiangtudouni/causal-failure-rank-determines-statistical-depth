module

public import Paid.PDROC_D27Prepare_FloorRun_001
public import Paid.PDROC_D27Prepare_TailBounds_001
public import Paid.PDROC_D27Prepare_Resources_010
public import Paid.PDROC_D27Prepare_Q_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.D27Prepare.FloorBounds

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute linearExecute_append)
open Program Memory Tail TailBounds Resources FloorRun

theorem floor_semantic_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (hz : Has memory 12 (.rational (P.zeroChargeRisk fee)))
    (hr : Has memory 3 (.rational P.certificate.risk))
    (hf : Has memory 43 (.rational (P.firstChargeFloor fee))) :
    SequenceMemoryBounds positiveFloorCommands memory 64 (operandBudget P fee) := by
  let middle := memory.write 32 (.rational (P.zeroChargeRisk fee - P.certificate.risk))
  have first : (SlotCommand.rational .subtract 12 3 32).eval memory = some middle :=
    rational_eval memory .subtract 12 3 32 _ _ _ hz hr rfl
  have middleBound : MemoryBounds 64 (operandBudget P fee) middle :=
    bounded.write 32 (.rational (P.zeroChargeRisk fee - P.certificate.risk)) (by decide) (risk_gap_bits P fee)
  have firstFloor := Has.write_other memory 43 32 (.rational (P.firstChargeFloor fee))
    (.rational (P.zeroChargeRisk fee - P.certificate.risk)) hf (by decide)
  have gap : Has middle 32 (.rational (P.zeroChargeRisk fee - P.certificate.risk)) := Has.write_same _ _ _
  have second : (SlotCommand.rational .multiply 43 32 44).eval middle =
      some (positiveFloorNext memory P fee) :=
    rational_eval middle .multiply 43 32 44 _ _ _ firstFloor gap rfl
  have floorEncoding : ratEncodingBits (P.positiveValueFloor fee) ≤ dataWeight P fee := by
    unfold dataWeight
    omega
  have finalBound : MemoryBounds 64 (operandBudget P fee) (positiveFloorNext memory P fee) :=
    middleBound.write 44 (.rational (P.positiveValueFloor fee)) (by decide)
      (rational_data_bits P fee _ floorEncoding)
  exact SequenceMemoryBounds.cons _ _ _ middle _ _ bounded first
    (SequenceMemoryBounds.cons _ [] middle (positiveFloorNext memory P fee) _ _ middleBound second
      (SequenceMemoryBounds.nil _ _ _ finalBound))

/-- Every real state of the signed-floor branch has bounded operands,
including old/value/flag at the actual control boundary. -/
theorem signed_floor_bounded (input : List Cell) (P : Parameters) (fee : ℚ)
    (before : State) (memory : SlotMemory) (matched : MemoryMatch before memory)
    (location : before.pc = pc 37) (bounded : StateBounds 64 (operandBudget P fee) before)
    (hz : Has memory 12 (.rational (P.zeroChargeRisk fee)))
    (hr : Has memory 3 (.rational P.certificate.risk))
    (hf : Has memory 43 (.rational (P.firstChargeFloor fee)))
    (hzero : Has memory 16 (.rational 0)) :
    ∃ (after : State) (trace : List State), MemoryMatch after (positiveFloorNext memory P fee) ∧
      after.pc = (if (Comparison.less.rat 0 (P.positiveValueFloor fee)) then (pc 39) else (pc 38)) ∧
      after.output = before.output ∧ trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length = 29 ∧ trace.IsChain (fun a b => step program input a = some b) ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      (∀ state ∈ trace, Q.MemoryProgress {32, 44} before state) := by
  obtain ⟨arithmetic, terminal, after, trace, arithmeticMatch, arithmeticExecute, comparisonExecute,
    afterMatch, afterPc, afterEq, output, head, last, length, chain, members⟩ :=
    signed_floor_page_trace input P fee before memory matched location hz hr hf hzero
  have addresses : ∀ command ∈ positiveFloorCommands, CommandAddresses 64 command := by
    intro command member
    simp only [positiveFloorCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> norm_num [CommandAddresses]
  have addressBits := address_bits P fee
  have semantic := floor_semantic_bounds P fee memory
    (memory_of_state before memory 64 (operandBudget P fee) matched bounded) hz hr hf
  have arithmeticBounds := slotSequence_prefix_bounds positiveFloorCommands input before memory
    (positiveFloorNext memory P fee) 64 (operandBudget P fee) matched bounded addresses addressBits
    (positiveFloor_body_eval memory P fee hz hr hf) semantic
  have arithmeticBound := arithmeticBounds.final arithmeticExecute
  have floorHas : Has (positiveFloorNext memory P fee) 44 (.rational (P.positiveValueFloor fee)) :=
    Has.write_same _ _ _
  have zeroHas : Has (positiveFloorNext memory P fee) 16 (.rational 0) := by
    apply Has.write_other
    · exact Has.write_other memory 16 32 (.rational 0)
        (.rational (P.zeroChargeRisk fee - P.certificate.risk)) hzero (by decide)
    · decide
  have zeroSlot := match_has arithmetic (positiveFloorNext memory P fee) 16 (.rational 0) arithmeticMatch zeroHas
  have floorSlot := match_has arithmetic (positiveFloorNext memory P fee) 44
    (.rational (P.positiveValueFloor fee)) arithmeticMatch floorHas
  have enough : 2 ≤ operandBudget P fee := by
    have : 8 ≤ operandBudget P fee := by
      simpa only [natBits, show Nat.log2 64 = 6 by decide] using addressBits
    omega
  have comparisonBounds := ratCompareSlots_prefix_bounds input arithmetic 16 44 64 (operandBudget P fee)
    .less 0 (P.positiveValueFloor fee) arithmeticBound arithmeticMatch.base
    zeroSlot.1 floorSlot.1 zeroSlot.2 floorSlot.2 (by decide) (by decide) addressBits enough
  have fullBounds := LinearPrefixBounds.append input (slotSequenceCode positiveFloorCommands)
    (ratCompareSlots .less 16 44) before arithmetic 64 (operandBudget P fee)
    arithmeticExecute arithmeticBounds comparisonBounds
  rw [positiveFloor_compiled] at fullBounds
  have fullExecute : linearExecute input positiveFloorSetup before = some terminal := by
    rw [← positiveFloor_compiled, linearExecute_append, arithmeticExecute, Option.bind_some]
    exact comparisonExecute
  have writes : ∀ command ∈ positiveFloorCommands, Memory.target command ∈ ({32, 44} : Finset ℕ) := by
    intro command member
    simp only [positiveFloorCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  have arithmeticFrames := Q.sequence_prefix_memory {32, 44} positiveFloorCommands input before memory
    (positiveFloorNext memory P fee) matched (positiveFloor_body_eval memory P fee hz hr hf) writes
  have comparisonFrames : Q.LinearPrefixMemory {32, 44} input (ratCompareSlots .less 16 44) arithmetic := by
    intro count state actual
    apply Q.linearExecute_no_memory_write {32, 44} input _ arithmetic state _ actual
    intro instruction member
    have inFull := List.mem_of_mem_take member
    simp only [ratCompareSlots, PDLower.CalibrationCompute.loadSlot, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at inFull
    rcases inFull with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;> trivial
  have fullFrames := Q.LinearPrefixMemory.append {32, 44} input (slotSequenceCode positiveFloorCommands)
    (ratCompareSlots .less 16 44) before arithmetic arithmeticExecute arithmeticFrames comparisonFrames
  rw [positiveFloor_compiled] at fullFrames
  refine ⟨after, trace, afterMatch, afterPc, output, head, last, length, chain, ?_, ?_⟩
  · exact page_trace_bounds input positiveFloorSetup before terminal after after.pc 64 (operandBudget P fee)
      trace fullBounds fullExecute afterEq (by simpa only [show positiveFloorSetup.length = 27 from rfl] using members)
  · intro state member
    rcases members state member with same | ⟨count, _, actual⟩
    · subst state
      rw [afterEq]
      exact (fullFrames.final fullExecute).with_pc _
    · exact fullFrames count state actual

end PDROC.D27Prepare.FloorBounds
