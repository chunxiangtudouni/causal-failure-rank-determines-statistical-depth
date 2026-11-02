module

public import Paid.PDROC_D27Prepare_Tail_002
public import Paid.PDROC_D27Prepare_TailBounds_001
public import Paid.PDROC_D27Prepare_Resources_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.D27Prepare.Dyadic

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame
open Program Memory Tail TailBounds Resources

theorem cycle_bounded (input : List Cell) (P : Parameters) (fee : ℚ)
    (before : State) (memory : SlotMemory) (i : ℕ)
    (matched : MemoryMatch before memory) (location : before.pc = pc 22)
    (bounded : StateBounds 64 (operandBudget P fee) before) (hi : i < P.certificate.stages)
    (hN : Has memory 0 (.natural P.certificate.stages)) (hindex : Has memory 35 (.natural i))
    (hone : Has memory 14 (.natural 1)) (hhalf : Has memory 21 (.rational (1 / 2)))
    (hpower : Has memory 39 (.rational ((1 / 2 : ℚ) ^ i))) :
    ∃ (after : State) (trace : List State), MemoryMatch after (dyadicNext memory i) ∧
      after.pc = pc 22 ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧ trace.length = 30 ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      ∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state := by
  have comparison : Comparison.less.nat i P.certificate.stages = true := by simp [Comparison.nat, hi]
  let terminal := comparisonResult before 0 35 0 true
  let guarded : State := {terminal with pc := pc 23}
  have indexSlot := match_has before memory 35 (.natural i) matched hindex
  have stagesSlot := match_has before memory 0 (.natural P.certificate.stages) matched hN
  have guardRun := Search.nat_compare_page_trace input 22 (by decide) before location .less
    35 0 24 23 i P.certificate.stages rfl matched.base indexSlot stagesSlot
  simp [comparison] at guardRun
  obtain ⟨guardTrace, guardHead, guardLast, guardLength, guardChain,
    guardHeap, guardLive, guardFresh, guardOutput, guardPrefixes⟩ := guardRun
  have guardMatch : MemoryMatch guarded memory :=
    ⟨guardHeap.trans matched.heap, guardLive.trans matched.live, guardFresh.trans matched.base⟩
  have addressBits := address_bits P fee
  have enough : 2 ≤ operandBudget P fee := by
    have : 8 ≤ operandBudget P fee := by
      simpa only [natBits, show Nat.log2 64 = 6 by decide] using addressBits
    omega
  have guardBounds := natCompareSlots_prefix_bounds input before 35 0 64 (operandBudget P fee)
    .less i P.certificate.stages bounded matched.base indexSlot.1 stagesSlot.1 indexSlot.2 stagesSlot.2
    (by decide) (by decide) addressBits enough
  have guardExecute : linearExecute input (natCompareSlots .less 35 0) before = some terminal := by
    simpa only [terminal, comparison] using natCompareSlots_execute input before 0 35 0 i P.certificate.stages .less
      matched.base (by simpa using indexSlot.1) (by simpa using stagesSlot.1)
      (by simpa using indexSlot.2) (by simpa using stagesSlot.2)
  have guardedBound : StateBounds 64 (operandBudget P fee) guarded :=
    (guardBounds.final guardExecute).with_pc (pc 23)
  obtain ⟨after, updateTrace, afterMatch, afterPc, updateOutput, updateHead, updateLast,
    updateLength, updateChain, updatePrefixes, updateTerminal, updateExecute, afterEq⟩ :=
    dyadic_update_trace input guarded memory i guardMatch rfl hindex hone hpower hhalf
  have semantic := dyadic_semantic_bounds P fee memory i
    (memory_of_state guarded memory 64 (operandBudget P fee) guardMatch guardedBound)
    hi hindex hone hpower hhalf
  have addresses : ∀ command ∈ dyadicStepCommands, CommandAddresses 64 command := by
    intro command member
    simp only [dyadicStepCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> norm_num [CommandAddresses]
  have updateBounds := slotSequence_prefix_bounds dyadicStepCommands input guarded memory
    (dyadicNext memory i) 64 (operandBudget P fee) guardMatch guardedBound addresses addressBits
    (dyadic_body_eval memory i hindex hone hpower hhalf) semantic
  rw [dyadicStep_compiled] at updateBounds
  have afterBound : StateBounds 64 (operandBudget P fee) after := by
    rw [afterEq]
    exact (updateBounds.final updateExecute).with_pc (pc 22)
  have guardAll : ∀ state ∈ guardTrace, StateBounds 64 (operandBudget P fee) state := by
    intro state member
    rcases guardPrefixes state member with same | prefixRun
    · simpa [same, guarded, terminal] using guardedBound
    · obtain ⟨count, _, executed⟩ := prefixRun
      exact guardBounds count state executed
  have updateAll : ∀ state ∈ updateTrace, StateBounds 64 (operandBudget P fee) state := by
    intro state member
    rcases updatePrefixes state member with same | prefixRun
    · simpa only [same] using afterBound
    · obtain ⟨count, _, executed⟩ := prefixRun
      exact updateBounds count state executed
  refine ⟨after, joinTrace guardTrace updateTrace, afterMatch, afterPc,
    updateOutput.trans guardOutput,
    joinTrace_head guardTrace updateTrace before guarded guardHead guardLast updateHead,
    joinTrace_last guardTrace updateTrace after updateLast, ?_,
    joinTrace_chain program input guardTrace updateTrace guarded guardChain updateChain guardLast updateHead, ?_⟩
  · simp only [joinTrace, List.length_append, List.length_dropLast, guardLength, updateLength]
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact guardAll state (List.mem_of_mem_dropLast early)
    · exact updateAll state late

theorem exit_bounded (input : List Cell) (P : Parameters) (fee : ℚ)
    (before : State) (memory : SlotMemory)
    (matched : MemoryMatch before memory) (location : before.pc = pc 22)
    (bounded : StateBounds 64 (operandBudget P fee) before)
    (hN : Has memory 0 (.natural P.certificate.stages))
    (hindex : Has memory 35 (.natural P.certificate.stages)) :
    ∃ (after : State) (trace : List State), MemoryMatch after memory ∧
      after.pc = pc 24 ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧ trace.length = 9 ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      ∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state := by
  have indexSlot := match_has before memory 35 (.natural P.certificate.stages) matched hindex
  have stagesSlot := match_has before memory 0 (.natural P.certificate.stages) matched hN
  let terminal := comparisonResult before 0 35 0 false
  let after : State := {terminal with pc := pc 24}
  have comparison : Comparison.less.nat P.certificate.stages P.certificate.stages = false := by simp [Comparison.nat]
  have run := Search.nat_compare_page_trace input 22 (by decide) before location .less 35 0 24 23
    P.certificate.stages P.certificate.stages rfl matched.base indexSlot stagesSlot
  simp [comparison] at run
  obtain ⟨trace, head, last, length, chain, heap, live, fresh, output, members⟩ := run
  have addressBits := address_bits P fee
  have enough : 2 ≤ operandBudget P fee := by
    have : 8 ≤ operandBudget P fee := by
      simpa only [natBits, show Nat.log2 64 = 6 by decide] using addressBits
    omega
  have bounds := natCompareSlots_prefix_bounds input before 35 0 64 (operandBudget P fee)
    .less P.certificate.stages P.certificate.stages bounded matched.base indexSlot.1 stagesSlot.1 indexSlot.2 stagesSlot.2
    (by decide) (by decide) addressBits enough
  have executed : linearExecute input (natCompareSlots .less 35 0) before = some terminal := by
    simpa only [terminal, comparison] using natCompareSlots_execute input before 0 35 0
      P.certificate.stages P.certificate.stages .less matched.base
      (by simpa using indexSlot.1) (by simpa using stagesSlot.1)
      (by simpa using indexSlot.2) (by simpa using stagesSlot.2)
  have afterBound : StateBounds 64 (operandBudget P fee) after := (bounds.final executed).with_pc (pc 24)
  refine ⟨after, trace, ⟨heap.trans matched.heap, live.trans matched.live, fresh.trans matched.base⟩,
    rfl, output, head, last, length, chain, ?_⟩
  intro state member
  rcases members state member with same | prefixRun
  · simpa [same, after, terminal] using afterBound
  · obtain ⟨count, _, actual⟩ := prefixRun
    exact bounds count state actual

end PDROC.D27Prepare.Dyadic
