module

public import Paid.PDROC_D27Prepare_Search_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid
open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

namespace PDROC.D27Prepare.Search

open Program Memory

/-- Only the actual typed cells needed by a majority loop iteration. -/
structure MajorityReady (D : CertificateInput) (j : ℕ) (state : State) : Prop where
  fresh : state.register .fresh = .natural 0
  location : state.pc = Program.pc 2
  counter : SlotHas state 6 (.natural (2 * j + 1))
  two : SlotHas state 15 (.natural 2)
  varianceSquared : SlotHas state 26 (.rational (D.varianceBase ^ 2))
  threshold : SlotHas state 27 (.rational ((D.risk / (2 * (D.stages : ℚ))) ^ 2))
  power : SlotHas state 28 (.rational (D.varianceBase ^ (2 * j + 1)))

/-- One rejected majority candidate executes the real guard, its branch,
the two literal update macros, and the jump back. This has 29 transitions.
Every intermediate state has its own successful literal-prefix witness. -/
theorem majority_iteration_trace (input : List Cell) (D : CertificateInput) (j : ℕ)
    (rejected : j < majorityIndex D) (before : State) (ready : MajorityReady D j before) :
    ∃ (middle after : State) (trace : List State), trace.head? = some before ∧
      trace.getLast? = some after ∧ trace.length = 30 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      MajorityReady D (j + 1) after ∧
      after.heap = Function.update
        (Function.update before.heap 6 (.natural (2 * (j + 1) + 1))) 28
        (.rational (D.varianceBase ^ (2 * (j + 1) + 1))) ∧
      after.live = before.live ∧ after.output = before.output ∧
      middle = {comparisonResult before 0 28 27
        (Comparison.rat .lessEqual (D.varianceBase ^ (2 * j + 1))
          ((D.risk / (2 * (D.stages : ℚ))) ^ 2)) with pc := Program.pc 3} ∧
      (∀ state ∈ trace,
        (state = middle ∨ ∃ count ≤ 7,
          linearExecute input (majorityGuard.take count) before = some state) ∨
        (state = after ∨ ∃ count ≤ 20,
          linearExecute input (majorityStep.take count) middle = some state)) ∧
      ∃ terminal : State, linearExecute input majorityStep middle = some terminal ∧
        after = {terminal with pc := Program.pc 2} := by
  obtain ⟨middle, first, firstHead, firstLast, firstLength, firstChain,
    middlePc, middleHeap, middleLive, middleFresh, middleOutput, firstPrefixes, middleExact⟩ :=
    majority_guard_page_trace input D j rejected.le before ready.location ready.fresh ready.power ready.threshold
  have middleLocation : middle.pc = Program.pc 3 := by
    simpa only [ite_eq_right (Nat.ne_of_lt rejected)] using middlePc
  have middleBase : middle.register .fresh = .natural 0 := middleFresh.trans ready.fresh
  let memory := currentMemory middle
  let counterMemory := memory.write 6 (.natural (2 * (j + 1) + 1))
  let next := counterMemory.write 28 (.rational (D.varianceBase ^ (2 * (j + 1) + 1)))
  have transfer (address : ℕ) (value : Cell) (old : SlotHas before address value) :
      Has memory address value := by
    simpa only [SlotHas, Has, memory, currentMemory, middleHeap, middleLive] using old
  have evaluated : slotSequenceEval majorityStepCommands memory = some next :=
    majorityStep_eval D j memory (transfer 6 _ ready.counter) (transfer 15 _ ready.two)
      (transfer 28 _ ready.power) (transfer 26 _ ready.varianceSquared)
  obtain ⟨after, later, afterMatch, afterPc, afterOutput, laterHead, laterLast,
    laterLength, laterChain, laterPrefixes, _terminal⟩ :=
    sequence_page_trace input 3 2 (by decide) majorityStepCommands rfl
      middle middleLocation memory next (currentMemory_match middle middleBase) evaluated
  have heap : after.heap = Function.update
      (Function.update before.heap 6 (.natural (2 * (j + 1) + 1))) 28
      (.rational (D.varianceBase ^ (2 * (j + 1) + 1))) := by
    simpa only [next, counterMemory, SlotMemory.write, memory, currentMemory, middleHeap] using afterMatch.heap
  have live : after.live = before.live := by
    have h : after.live = insert 28 (insert 6 before.live) := by
      simpa only [next, counterMemory, SlotMemory.write, memory, currentMemory, middleLive] using afterMatch.live
    simpa only [Finset.insert_eq_of_mem ready.counter.1, Finset.insert_eq_of_mem ready.power.1] using h
  have keep (address : ℕ) (value : Cell) (old : SlotHas before address value)
      (notCounter : address ≠ 6) (notPower : address ≠ 28) : SlotHas after address value := by
    apply match_has after next address value afterMatch
    exact Has.write_other counterMemory address 28 value _
      (Has.write_other memory address 6 value _ (transfer address value old) notCounter) notPower
  have afterReady : MajorityReady D (j + 1) after := by
    refine ⟨afterMatch.base, afterPc, ?_, keep 15 _ ready.two (by decide) (by decide),
      keep 26 _ ready.varianceSquared (by decide) (by decide),
      keep 27 _ ready.threshold (by decide) (by decide), ?_⟩
    · apply match_has after next 6 _ afterMatch
      exact Has.write_other counterMemory 6 28 _ _ (Has.write_same memory 6 _) (by decide)
    · exact match_has after next 28 _ afterMatch (Has.write_same counterMemory 28 _)
  refine ⟨middle, after, joinTrace first later,
    joinTrace_head first later before middle firstHead firstLast laterHead,
    joinTrace_last first later after laterLast, ?_,
    joinTrace_chain Program.program input first later middle firstChain laterChain firstLast laterHead,
    afterReady, heap, live, afterOutput.trans middleOutput, ?_, ?_, ?_⟩
  · have laterSize : later.length = 22 := by
      simpa [majorityStepCommands, slotSequenceCode, SlotCommand.code, natBinarySlots,
        PDCompute.Solver.ratBinarySlots, PDLower.CalibrationCompute.loadSlot,
        PDLower.CalibrationCompute.storeSlot] using laterLength
    simp only [joinTrace, List.length_append, List.length_dropLast, firstLength, laterSize]
  · simpa only [ite_eq_right (Nat.ne_of_lt rejected)] using middleExact
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact Or.inl (firstPrefixes state (List.mem_of_mem_dropLast early))
    · apply Or.inr
      simpa only [majorityStep_compiled, show majorityStep.length = 20 from rfl] using laterPrefixes state late
  · simpa only [majorityStep_compiled] using _terminal

end PDROC.D27Prepare.Search
