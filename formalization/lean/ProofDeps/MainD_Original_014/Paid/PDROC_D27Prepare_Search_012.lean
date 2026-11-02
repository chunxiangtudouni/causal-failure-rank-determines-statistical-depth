module

public import Paid.PDROC_D27Prepare_Search_008
public import Paid.PDROC_D27Prepare_Resources_011
public import Paid.PDROC_D27Prepare_Resources_009
public import Paid.PDROC_D27Prepare_Resources_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)

namespace PDROC.D27Prepare.Search

open Program Memory

/-- Uniform all-register/live-cell/output-cell bound for one actual
majority iteration. The same budget is preserved, without multiplying it
once per iteration. Powers are bounded at their true exponent. -/
theorem majority_iteration_bounded_trace (input : List Cell) (P : Parameters) (fee : ℚ) (j : ℕ)
    (rejected : j < majorityIndex P.certificate) (before : State)
    (ready : MajorityReady P.certificate j before)
    (bounded : Resources.StateBounds 64 (Resources.operandBudget P fee) before) :
    ∃ (after : State) (trace : List State), trace.head? = some before ∧
      trace.getLast? = some after ∧ trace.length = 30 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      MajorityReady P.certificate (j + 1) after ∧
      after.heap = Function.update
        (Function.update before.heap 6 (.natural (2 * (j + 1) + 1))) 28
        (.rational (P.certificate.varianceBase ^ (2 * (j + 1) + 1))) ∧
      after.live = before.live ∧ after.output = before.output ∧
      ∀ state ∈ trace, Resources.StateBounds 64 (Resources.operandBudget P fee) state := by
  let B := Resources.operandBudget P fee
  obtain ⟨middle, after, trace, head, last, length, chain, afterReady, afterHeap,
    afterLive, afterOutput, middleExact, origins, terminalWitness⟩ :=
    majority_iteration_trace input P.certificate j rejected before ready
  have addressBits := Resources.operandBudget_address_bits P fee
  have enough : 2 ≤ B := by
    have h := Resources.linear_le_operandBudget P fee
    omega
  let guardTerminal := comparisonResult before 0 28 27
    (Comparison.rat .lessEqual (P.certificate.varianceBase ^ (2 * j + 1))
      ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2))
  have guardBounds : Resources.LinearPrefixBounds input majorityGuard before 64 B :=
    Resources.ratCompareSlots_prefix_bounds input before 28 27 64 B .lessEqual
      (P.certificate.varianceBase ^ (2 * j + 1))
      ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2)
      bounded ready.fresh ready.power.1 ready.threshold.1 ready.power.2 ready.threshold.2
      (by decide) (by decide) addressBits enough
  have guardExecuted : linearExecute input majorityGuard before = some guardTerminal :=
    ratCompareSlots_execute input before 0 28 27
      (P.certificate.varianceBase ^ (2 * j + 1))
      ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2) .lessEqual ready.fresh
      ready.power.1 ready.threshold.1
      ready.power.2 ready.threshold.2
  have middleBounds : Resources.StateBounds 64 B middle := by
    rw [middleExact]
    exact (guardBounds.final guardExecuted).with_pc (pc 3)
  have comparisonFields := comparisonResult_fields before 0 28 27
    (Comparison.rat .lessEqual (P.certificate.varianceBase ^ (2 * j + 1))
      ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2))
  have middleHeap : middle.heap = before.heap := by rw [middleExact]; exact comparisonFields.1
  have middleLive : middle.live = before.live := by rw [middleExact]; exact comparisonFields.2.1
  have middleFresh : middle.register .fresh = .natural 0 := by
    rw [middleExact]
    exact comparisonFields.2.2.1.trans ready.fresh
  let memory := currentMemory middle
  let nextCounter := 2 * (j + 1) + 1
  let counterMemory := memory.write 6 (.natural nextCounter)
  let next := counterMemory.write 28 (.rational (P.certificate.varianceBase ^ nextCounter))
  have memoryHas (address : ℕ) (value : Cell) (old : SlotHas before address value) :
      Has memory address value := by
    simpa only [SlotHas, Has, memory, currentMemory, middleHeap, middleLive] using old
  have matched : MemoryMatch middle memory := currentMemory_match middle middleFresh
  have memoryBounds : Resources.MemoryBounds 64 B memory :=
    ⟨middleBounds.live, middleBounds.heapValues⟩
  have counterRange : nextCounter ≤ P.certificate.t0 :=
    majority_counter_le P.certificate (j + 1) (by omega)
  have indexBound : nextCounter ≤ Resources.dataWeight P fee :=
    counterRange.trans (Resources.scalar_data_bounds P fee).2.1
  have counterBits : (Cell.natural nextCounter).bits ≤ B :=
    Resources.natural_small_bits P fee nextCounter (by omega)
  have powerBits : (Cell.rational (P.certificate.varianceBase ^ nextCounter)).bits ≤ B :=
    Resources.bounded_power_bits P fee P.certificate.varianceBase nextCounter
      (Resources.search_base_encodings P fee).1 indexBound
  have counterMemoryBounds := memoryBounds.write 6 (.natural nextCounter) (by decide) counterBits
  have nextBounds := counterMemoryBounds.write 28
    (.rational (P.certificate.varianceBase ^ nextCounter)) (by decide) powerBits
  have firstEval : (SlotCommand.natural .add 6 15 6).eval memory = some counterMemory := by
    apply natural_eval memory .add 6 15 6 (2 * j + 1) 2 nextCounter
      (memoryHas 6 _ ready.counter) (memoryHas 15 _ ready.two)
    simp only [NatOp.eval, Option.some.injEq]
    dsimp only [nextCounter]
    omega
  have powerHas : Has counterMemory 28 (.rational (P.certificate.varianceBase ^ (2 * j + 1))) :=
    Has.write_other memory 28 6 _ _ (memoryHas 28 _ ready.power) (by decide)
  have squareHas : Has counterMemory 26 (.rational (P.certificate.varianceBase ^ 2)) :=
    Has.write_other memory 26 6 _ _ (memoryHas 26 _ ready.varianceSquared) (by decide)
  have secondEval : (SlotCommand.rational .multiply 28 26 28).eval counterMemory = some next := by
    apply rational_eval counterMemory .multiply 28 26 28 _ _ _ powerHas squareHas
    simp only [RatOp.eval, Option.some.injEq]
    exact (majority_power_step P.certificate j).symm
  have semantic : Resources.SequenceMemoryBounds majorityStepCommands memory 64 B :=
    Resources.SequenceMemoryBounds.cons (.natural .add 6 15 6) [.rational .multiply 28 26 28]
      memory counterMemory 64 B memoryBounds firstEval
      (Resources.SequenceMemoryBounds.cons (.rational .multiply 28 26 28) []
        counterMemory next 64 B counterMemoryBounds secondEval
        (Resources.SequenceMemoryBounds.nil next 64 B nextBounds))
  have executed : slotSequenceEval majorityStepCommands memory = some next :=
    majorityStep_eval P.certificate j memory (memoryHas 6 _ ready.counter) (memoryHas 15 _ ready.two)
      (memoryHas 28 _ ready.power) (memoryHas 26 _ ready.varianceSquared)
  have addresses : ∀ command ∈ majorityStepCommands, Resources.CommandAddresses 64 command := by
    intro command member
    simp only [majorityStepCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> norm_num [Resources.CommandAddresses]
  have stepBounds : Resources.LinearPrefixBounds input majorityStep middle 64 B := by
    have h := Resources.slotSequence_prefix_bounds majorityStepCommands input middle memory next 64 B
      matched middleBounds addresses addressBits executed semantic
    simpa only [majorityStep_compiled] using h
  obtain ⟨terminal, terminalExecuted, finalState⟩ := terminalWitness
  have finalBounds : Resources.StateBounds 64 B after := by
    rw [finalState]
    exact (stepBounds.final terminalExecuted).with_pc (pc 2)
  refine ⟨after, trace, head, last, length, chain, afterReady, afterHeap, afterLive, afterOutput, ?_⟩
  intro state member
  rcases origins state member with guardState | stepState
  · rcases guardState with same | ⟨count, _, actual⟩
    · subst state
      exact middleBounds
    · exact guardBounds count state actual
  · rcases stepState with same | ⟨count, _, actual⟩
    · subst state
      exact finalBounds
    · exact stepBounds count state actual

end PDROC.D27Prepare.Search
