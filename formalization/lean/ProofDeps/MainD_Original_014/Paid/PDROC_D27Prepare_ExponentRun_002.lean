module

public import Paid.PDROC_D27Prepare_ExponentRun_001
public import Paid.PDROC_D27Prepare_Resources_011
public import Paid.PDROC_D27Prepare_Resources_014
public import Paid.PDROC_D27Prepare_J_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.ExponentRun

def setupMemory (P : Parameters) (memory : SlotMemory) : SlotMemory :=
  ((memory.write 32 (.rational P.certificate.epsilon)).write 31
    (.rational (P.certificate.gamma*P.certificate.epsilon))).write 28 (.rational (1/2))

theorem setup_eval (P : Parameters) (memory : SlotMemory)
    (menu : Has memory 29 (.rational P.certificate.menuRatio))
    (three : Has memory 19 (.rational 3)) (gamma : Has memory 2 (.rational P.certificate.gamma))
    (half : Has memory 21 (.rational (1/2))) :
    slotSequenceEval exponentSetupCommands memory=some (setupMemory P memory) := by
  let m1 := memory.write 32 (.rational P.certificate.epsilon)
  let m2 := m1.write 31 (.rational (P.certificate.gamma*P.certificate.epsilon))
  have e1 : (SlotCommand.rational .divide 29 19 32).eval memory=some m1 :=
    rational_eval memory .divide 29 19 32 _ _ _ menu three
      (by simp [RatOp.eval,CertificateInput.epsilon])
  have e2 : (SlotCommand.rational .multiply 2 32 31).eval m1=some m2 :=
    rational_eval m1 .multiply 2 32 31 _ _ _
      (by simpa [m1,Has,SlotMemory.write] using gamma) (Has.write_same memory 32 _) rfl
  have e3 : (SlotCommand.copy 21 28).eval m2=some (setupMemory P memory) :=
    copy_eval m2 21 28 _ (by simpa [m2,m1,Has,SlotMemory.write] using half)
  simp only [exponentSetupCommands,slotSequenceEval,e1,Option.bind_some,e2,e3]

theorem setup_memory_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (menu : Has memory 29 (.rational P.certificate.menuRatio))
    (three : Has memory 19 (.rational 3)) (gamma : Has memory 2 (.rational P.certificate.gamma))
    (half : Has memory 21 (.rational (1/2))) :
    SequenceMemoryBounds exponentSetupCommands memory 64 (operandBudget P fee) := by
  let m1 := memory.write 32 (.rational P.certificate.epsilon)
  let m2 := m1.write 31 (.rational (P.certificate.gamma*P.certificate.epsilon))
  let m3 := m2.write 28 (.rational (1/2))
  have menuBits := (search_base_encodings P fee).2.2.1
  have threeBits : ratEncodingBits (3 : ℚ)=4 := by
    norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have divisionBits := ratEncodingBits_div_le P.certificate.menuRatio (3 : ℚ)
  have epsilonBits : (Cell.rational P.certificate.epsilon).bits≤operandBudget P fee := by
    apply le_trans (b:=64*(dataWeight P fee+1)) _ (linear_le_operandBudget P fee)
    change 1+ratEncodingBits (P.certificate.menuRatio/(3 : ℚ))≤64*(dataWeight P fee+1)
    omega
  have thresholdBits := (search_base_encodings P fee).2.2.2.1
  have resultBits : (Cell.rational (P.certificate.gamma*P.certificate.epsilon)).bits≤operandBudget P fee := by
    apply le_trans (b:=64*(dataWeight P fee+1)) _ (linear_le_operandBudget P fee)
    change 1+ratEncodingBits (P.certificate.gamma*P.certificate.epsilon)≤64*(dataWeight P fee+1)
    omega
  have b1 : MemoryBounds 64 (operandBudget P fee) m1 := bounded.write 32 _ (by decide) epsilonBits
  have b2 : MemoryBounds 64 (operandBudget P fee) m2 := b1.write 31 _ (by decide) resultBits
  have b3 : MemoryBounds 64 (operandBudget P fee) m3 := b2.write 28 _ (by decide)
    (by simpa only [half.2] using bounded.values 21 half.1)
  have e1 : (SlotCommand.rational .divide 29 19 32).eval memory=some m1 :=
    rational_eval memory .divide 29 19 32 _ _ _ menu three
      (by simp [RatOp.eval,CertificateInput.epsilon])
  have e2 : (SlotCommand.rational .multiply 2 32 31).eval m1=some m2 :=
    rational_eval m1 .multiply 2 32 31 _ _ _
      (by simpa [m1,Has,SlotMemory.write] using gamma) (Has.write_same memory 32 _) rfl
  have e3 : (SlotCommand.copy 21 28).eval m2=some m3 :=
    copy_eval m2 21 28 _ (by simpa [m2,m1,Has,SlotMemory.write] using half)
  exact SequenceMemoryBounds.cons _ _ memory m1 64 _ bounded e1
    (SequenceMemoryBounds.cons _ _ m1 m2 64 _ b1 e2
      (SequenceMemoryBounds.cons _ [] m2 m3 64 _ b2 e3 (SequenceMemoryBounds.nil m3 64 _ b3)))

theorem setup_data (P : Parameters) (memory : SlotMemory)
    (counter : Has memory 8 (.natural 1)) (one : Has memory 14 (.natural 1))
    (half : Has memory 21 (.rational (1/2))) : ExponentData P (setupMemory P memory) 1 := by
  constructor
  · simpa [Has,setupMemory,SlotMemory.write] using counter
  · simpa [Has,setupMemory,SlotMemory.write] using one
  · simpa [Has,setupMemory,SlotMemory.write] using half
  · simp [Has,setupMemory,SlotMemory.write]
  · simp [Has,setupMemory,SlotMemory.write]

theorem setup_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (initial : ExponentInitial P fee before) (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State,MemoryMatch after (setupMemory P (Search.currentMemory before)) ∧ after.pc=pc 8 ∧
      ExponentData P (setupMemory P (Search.currentMemory before)) 1 ∧
      Segment region input before after 64 (operandBudget P fee) 28 := by
  let memory := Search.currentMemory before
  have matched := Search.currentMemory_match before initial.raw.fresh
  have memoryBound := MemoryMatch.memoryBounds before memory 64 _ matched bounded
  have addresses : ∀ command∈exponentSetupCommands,CommandAddresses 64 command := by
    intro command member
    simp only [exponentSetupCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command∈exponentSetupCommands,Memory.target command∈region := by
    intro command member
    simp only [exponentSetupCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> simp [Memory.target,region]
  obtain ⟨after,afterMatch,afterPc,segment⟩ := J.sequence_page_segment region input (operandBudget P fee)
    7 8 (by decide) exponentSetupCommands rfl before initial.location memory (setupMemory P memory) matched
    (setup_eval P memory initial.menuRatio initial.raw.ratThree initial.raw.gamma initial.raw.ratHalf)
    bounded (setup_memory_bounds P fee memory memoryBound initial.menuRatio initial.raw.ratThree
      initial.raw.gamma initial.raw.ratHalf) (operandBudget_address_bits P fee) addresses writes
  exact ⟨after,afterMatch,afterPc,setup_data P memory initial.E initial.raw.natOne initial.raw.ratHalf,segment⟩

end PDROC.D27Prepare.ExponentRun
