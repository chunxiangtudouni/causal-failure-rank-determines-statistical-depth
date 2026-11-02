module

public import Paid.PDROC_D27Prepare_ExponentRun_002
public import Paid.PDROC_D27Prepare_Tail_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.ExponentRun

theorem step_memory_bounds (P : Parameters) (fee : ℚ) (memory : SlotMemory) (e : ℕ)
    (bounded : MemoryBounds 64 (operandBudget P fee) memory)
    (range : e<P.certificate.E) (data : ExponentData P memory e) :
    SequenceMemoryBounds exponentStepCommands memory 64 (operandBudget P fee) := by
  let m1 := memory.write 8 (.natural (e+1))
  let m2 := stepMemory memory e
  have count := (scalar_data_bounds P fee).2.2.2.1
  have b1 : MemoryBounds 64 (operandBudget P fee) m1 := bounded.write 8 _ (by decide)
    (natural_small_bits P fee (e+1) (by omega))
  have b2 : MemoryBounds 64 (operandBudget P fee) m2 := b1.write 28 _ (by decide)
    (exponent_power_bits P fee (e+1) (by omega))
  have first : (SlotCommand.natural .add 8 14 8).eval memory=some m1 :=
    natural_eval memory .add 8 14 8 e 1 (e+1) data.counter data.one rfl
  have later : (SlotCommand.rational .multiply 28 21 28).eval m1=some m2 :=
    rational_eval m1 .multiply 28 21 28 _ _ _
      (by simpa [m1,Has,SlotMemory.write] using data.power)
      (by simpa [m1,Has,SlotMemory.write] using data.half)
      (by
        simp only [RatOp.eval,Option.some.injEq]
        simpa only [one_div,inv_pow] using (Search.exponent_power_step e).symm)
  exact SequenceMemoryBounds.cons _ _ memory m1 64 _ bounded first
    (SequenceMemoryBounds.cons _ [] m1 m2 64 _ b1 later (SequenceMemoryBounds.nil m2 64 _ b2))

theorem step_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (e : ℕ) (matched : MemoryMatch before memory)
    (location : before.pc=pc 9) (bounded : StateBounds 64 (operandBudget P fee) before)
    (range : e<P.certificate.E) (data : ExponentData P memory e) :
    ∃ after : State,MemoryMatch after (stepMemory memory e) ∧ after.pc=pc 8 ∧
      Segment region input before after 64 (operandBudget P fee) 22 := by
  have addresses : ∀ command∈exponentStepCommands,CommandAddresses 64 command := by
    intro command member
    simp only [exponentStepCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command∈exponentStepCommands,Memory.target command∈region := by
    intro command member
    simp only [exponentStepCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> simp [Memory.target,region]
  simpa only [show (slotSequenceCode exponentStepCommands).length=20 from rfl] using
    J.sequence_page_segment region input (operandBudget P fee) 9 8 (by decide) exponentStepCommands rfl
      before location memory (stepMemory memory e) matched
      (Search.exponentStep_eval e memory data.counter data.one data.power data.half) bounded
      (step_memory_bounds P fee memory e (MemoryMatch.memoryBounds before memory 64 _ matched bounded) range data)
      (operandBudget_address_bits P fee) addresses writes

theorem guard_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (e : ℕ) (matched : MemoryMatch before memory)
    (location : before.pc=pc 8) (bounded : StateBounds 64 (operandBudget P fee) before)
    (positive : 1≤e) (range : e≤P.certificate.E) (data : ExponentData P memory e) :
    ∃ after : State,MemoryMatch after memory ∧
      after.pc=(if e=P.certificate.E then pc 10 else pc 9) ∧
      Segment region input before after 64 (operandBudget P fee) 9 := by
  have addressBits := operandBudget_address_bits P fee
  have enough : 2≤operandBudget P fee := by
    have address : 1+natBits 64=8 := by decide
    omega
  obtain ⟨after,afterPc,heap,live,segment⟩ := Tail.rat_compare_segment region input 8 (by decide)
    before location .lessEqual 28 31 9 10 ((1/2 : ℚ)^e) (P.certificate.gamma*P.certificate.epsilon)
    rfl matched.base (match_has before memory 28 _ matched data.power)
    (match_has before memory 31 _ matched data.threshold) _ bounded addressBits (by decide) (by decide) enough
  have exactGuard := Search.exponent_guard_boolean P.certificate e positive range
  have position : after.pc=(if e=P.certificate.E then pc 10 else pc 9) := by
    simpa only [exactGuard,decide_eq_true_eq] using afterPc
  exact ⟨after,⟨heap.trans matched.heap,live.trans matched.live,segment.fresh.trans matched.base⟩,position,segment⟩

end PDROC.D27Prepare.ExponentRun
