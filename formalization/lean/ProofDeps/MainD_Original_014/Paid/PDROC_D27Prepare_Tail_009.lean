module

public import Paid.PDROC_D27Prepare_Tail_004
public import Paid.PDROC_D27Prepare_Tail_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.Tail

theorem nonzero_zeta_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (matched : MemoryMatch before memory)
    (location : before.pc=pc 25) (bounded : StateBounds 64 (operandBudget P fee) before)
    (nonzero : fee≠0) (hone : Has memory 17 (.rational 1))
    (hpower : Has memory 39 (.rational ((1/2 : ℚ)^P.certificate.stages))) :
    ∃ after : State,MemoryMatch after (memory.write 12 (.rational (P.zeroChargeRisk fee))) ∧
      after.pc=pc 32 ∧ Segment binomialRegion input before after 64 (operandBudget P fee) 12 := by
  let next := memory.write 12 (.rational (P.zeroChargeRisk fee))
  have memoryBound := MemoryMatch.memoryBounds before memory 64 _ matched bounded
  have bits : (Cell.rational (P.zeroChargeRisk fee)).bits≤operandBudget P fee :=
    preparedInput_cell_bits P fee _ (by simp [preparedInput])
  have nextBound := memoryBound.write 12 _ (by decide) bits
  have first : (SlotCommand.rational .subtract 17 39 12).eval memory=some next := by
    apply rational_eval memory .subtract 17 39 12 1 ((1/2 : ℚ)^P.certificate.stages)
      (P.zeroChargeRisk fee) hone hpower
    simp [RatOp.eval,zeroChargeRisk,nonzero]
  have semantic : SequenceMemoryBounds nonzeroZetaCommands memory 64 (operandBudget P fee) :=
    SequenceMemoryBounds.cons _ [] memory next 64 _ memoryBound first
      (SequenceMemoryBounds.nil next 64 _ nextBound)
  have addresses : ∀ command∈nonzeroZetaCommands,CommandAddresses 64 command := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    norm_num [CommandAddresses]
  have writes : ∀ command∈nonzeroZetaCommands,Memory.target command∈binomialRegion := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    simp [Memory.target,binomialRegion]
  simpa only [show (slotSequenceCode nonzeroZetaCommands).length=10 from rfl] using
    J.sequence_page_segment binomialRegion input (operandBudget P fee) 25 32 (by decide)
      nonzeroZetaCommands rfl before location memory next matched
      (nonzero_zeta_eval memory P fee nonzero hone hpower) bounded semantic
      (operandBudget_address_bits P fee) addresses writes

theorem zero_zeta_segment (P : Parameters) (input : List Cell)
    (before : State) (memory : SlotMemory) (matched : MemoryMatch before memory)
    (location : before.pc=pc 31) (bounded : StateBounds 64 (operandBudget P 0) before)
    (data : BinomialData P memory (P.certificate.stages+1)) :
    ∃ after : State,MemoryMatch after (memory.write 12 (.rational (P.zeroChargeRisk 0))) ∧
      after.pc=pc 32 ∧ Segment binomialRegion input before after 64 (operandBudget P 0) 12 := by
  let next := memory.write 12 (.rational (P.zeroChargeRisk 0))
  have memoryBound := MemoryMatch.memoryBounds before memory 64 _ matched bounded
  have bits : (Cell.rational (P.zeroChargeRisk 0)).bits≤operandBudget P 0 :=
    preparedInput_cell_bits P 0 _ (by simp [preparedInput])
  have nextBound := memoryBound.write 12 _ (by decide) bits
  have first : (SlotCommand.rational .multiply 42 39 12).eval memory=some next := by
    apply rational_eval memory .multiply 42 39 12 _ _ (P.zeroChargeRisk 0) data.tail data.dyadic
    simp only [RatOp.eval,Binomial.original_zeta_fee_zero]
  have semantic : SequenceMemoryBounds zeroZetaCommands memory 64 (operandBudget P 0) :=
    SequenceMemoryBounds.cons _ [] memory next 64 _ memoryBound first
      (SequenceMemoryBounds.nil next 64 _ nextBound)
  have addresses : ∀ command∈zeroZetaCommands,CommandAddresses 64 command := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    norm_num [CommandAddresses]
  have writes : ∀ command∈zeroZetaCommands,Memory.target command∈binomialRegion := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    simp [Memory.target,binomialRegion]
  simpa only [show (slotSequenceCode zeroZetaCommands).length=10 from rfl] using
    J.sequence_page_segment binomialRegion input (operandBudget P 0) 31 32 (by decide)
      zeroZetaCommands rfl before location memory next matched
      (zero_zeta_eval memory P data.tail data.dyadic) bounded semantic
      (operandBudget_address_bits P 0) addresses writes

/-- Original fee-zero/nonzero branches, including the complete N+1
binomial loop. K only participates in the actual comparison, not fuel. -/
theorem original_zeta_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (matched : MemoryMatch before memory)
    (location : before.pc=pc 24) (bounded : StateBounds 64 (operandBudget P fee) before)
    (hN : Has memory 0 (.natural P.certificate.stages)) (hK : Has memory 1 (.natural P.tools))
    (hfee : Has memory 5 (.rational fee)) (hzero : Has memory 13 (.natural 0))
    (hone : Has memory 14 (.natural 1)) (hrzero : Has memory 16 (.rational 0))
    (hrone : Has memory 17 (.rational 1))
    (hpower : Has memory 39 (.rational ((1/2 : ℚ)^P.certificate.stages))) :
    ∃ (after : State) (finalMemory : SlotMemory),MemoryMatch after finalMemory ∧
      Has finalMemory 12 (.rational (P.zeroChargeRisk fee)) ∧ after.pc=pc 32 ∧
      Segment binomialRegion input before after 64 (operandBudget P fee)
        (100*(P.certificate.stages+1)+50) := by
  have addressBits := operandBudget_address_bits P fee
  have enough : 2≤operandBudget P fee := by
    have address : 1+natBits 64=8 := by decide
    omega
  obtain ⟨guarded,guardPc,guardHeap,guardLive,guardSegment⟩ :=
    rat_compare_segment binomialRegion input 24 (by decide) before location .equal 5 16 25 26 fee 0 rfl
      matched.base (match_has before memory 5 _ matched hfee) (match_has before memory 16 _ matched hrzero)
      _ bounded addressBits (by decide) (by decide) enough
  have guardMatch : MemoryMatch guarded memory :=
    ⟨guardHeap.trans matched.heap,guardLive.trans matched.live,guardSegment.fresh.trans matched.base⟩
  by_cases zeroFee : fee=0
  · subst fee
    have start26 : guarded.pc=pc 26 := by simpa [Comparison.rat] using guardPc
    obtain ⟨initialized,initMatch,initPc,initSegment⟩ :=
      binomial_setup_segment P 0 input guarded memory guardMatch start26 guardSegment.final_bounds hzero hrone hrzero
    obtain ⟨scanned,scanMemory,scanMatch,scanData,scanPc,scanSegment⟩ :=
      binomial_loop_segment P 0 input (P.certificate.stages+1) 0 initialized (binomialInitial memory)
        (by omega) initMatch initPc initSegment.final_bounds
        (binomial_initial_data P memory hN hK hzero hone hrzero hrone hpower)
    obtain ⟨after,afterMatch,afterPc,finishSegment⟩ :=
      zero_zeta_segment P input scanned scanMemory scanMatch scanPc scanSegment.final_bounds scanData
    exact ⟨after,scanMemory.write 12 (.rational (P.zeroChargeRisk 0)),afterMatch,Has.write_same _ _ _,afterPc,
      (((guardSegment.trans initSegment).trans scanSegment).trans finishSegment).weaken_budget (by omega)⟩
  · have start25 : guarded.pc=pc 25 := by simpa [Comparison.rat,zeroFee] using guardPc
    obtain ⟨after,afterMatch,afterPc,finishSegment⟩ :=
      nonzero_zeta_segment P fee input guarded memory guardMatch start25 guardSegment.final_bounds zeroFee hrone hpower
    exact ⟨after,memory.write 12 (.rational (P.zeroChargeRisk fee)),afterMatch,Has.write_same _ _ _,afterPc,
      (guardSegment.trans finishSegment).weaken_budget (by omega)⟩

end PDROC.D27Prepare.Tail
