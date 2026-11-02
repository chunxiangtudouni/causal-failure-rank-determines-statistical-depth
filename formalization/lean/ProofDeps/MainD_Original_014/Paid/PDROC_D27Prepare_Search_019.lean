module

public import Paid.PDROC_D27Prepare_Search_014
public import Paid.PDROC_D27Prepare_Search_015
public import Paid.PDROC_D27Prepare_Search_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Search

/-- Actual boundary before the endpoint search setup. Scratch values
for the endpoint ratio/odds and exponent threshold are not supplied. -/
structure EndpointInitial (P : Parameters) (fee : ℚ) (state : State) : Prop where
  raw : RawConstants P fee state
  location : state.pc = pc 4
  t0 : SlotHas state 6 (.natural P.certificate.t0)
  M : SlotHas state 7 (.natural 0)
  E : SlotHas state 8 (.natural 1)
  Q : SlotHas state 9 (.natural 1)
  ratStages : SlotHas state 22 (.rational P.certificate.stages)
  gammaSquared : SlotHas state 24 (.rational (P.certificate.gamma ^ 2))
  variance : SlotHas state 25 (.rational P.certificate.varianceBase)
  varianceSquared : SlotHas state 26 (.rational (P.certificate.varianceBase ^ 2))
  majorityThreshold : SlotHas state 27 (.rational ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2))

/-- The first complete original search from raw6. Neither its initial
computed powers nor the least odd t0 nor any successful trace is an input. -/
theorem raw_majority_trace (P : Parameters) (fee : ℚ) :
    ∃ (after : State) (trace : List State), EndpointInitial P fee after ∧
      after.output = [] ∧ trace.head? = some initial ∧ trace.getLast? = some after ∧
      trace.IsChain (fun a b => step program (rawInput P fee) a = some b) ∧
      trace.length ≤ 200 + 29 * majorityIndex P.certificate ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) := by
  obtain ⟨entry, entryTrace, entryReady, entryOutput, entryHead, entryLast, entryLength, entryChain, entryBounds⟩ :=
    raw_initial_trace P fee
  let memory := currentMemory entry
  have matched : MemoryMatch entry memory := currentMemory_match entry entryReady.raw.fresh
  have old (address : ℕ) (value : Cell) (stored : SlotHas entry address value) : Has memory address value :=
    has_of_match entry memory address value matched stored
  obtain ⟨loopState, setupMatch, loopReady, setupSegment⟩ := majority_setup_segment P fee (rawInput P fee)
    entry memory matched entryReady (entryBounds entry (List.mem_of_getLast? entryLast))
  obtain ⟨after, loopTrace, afterPc, afterFresh, afterCounter, loopHead, loopLast, loopChain,
    loopLength, loopBounds, afterLive, afterOutput, afterHeap⟩ :=
    majority_loop_trace (rawInput P fee) P fee (majorityIndex P.certificate) 0 (by omega)
      loopState loopReady setupSegment.final_bounds
  have setupRaw : RawConstants P fee loopState := RawConstants.transport P fee entry loopState entryReady.raw
    (by
      intro address read
      apply setupSegment.final_frame.1.1 address
      simp only [searchRegion, Finset.mem_insert, Finset.mem_singleton]
      omega)
    setupSegment.final_frame.2 setupSegment.fresh
  have finalRaw : RawConstants P fee after := RawConstants.transport P fee loopState after setupRaw
    (by intro address read; exact afterHeap address (by omega) (by omega))
    (by intro address member; simpa only [afterLive] using member)
    (afterFresh.trans setupRaw.fresh.symm)
  have get (address : ℕ) (notCounter : address ≠ 6) (notPower : address ≠ 28)
      (value : Cell) (stored : Has (majoritySetupMemory P.certificate memory) address value) :
      SlotHas after address value := SlotHas_of_heap_live loopState after address value
        (match_has loopState _ address value setupMatch stored) (afterHeap address notCounter notPower)
        (fun member => by simpa only [afterLive] using member)
  have endpoint : EndpointInitial P fee after := by
    refine ⟨finalRaw, afterPc, afterCounter, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply get 7 (by decide) (by decide)
      simpa [majoritySetupMemory, Has, SlotMemory.write] using old 7 _ entryReady.M
    · apply get 8 (by decide) (by decide)
      simpa [majoritySetupMemory, Has, SlotMemory.write] using old 8 _ entryReady.E
    · apply get 9 (by decide) (by decide)
      simpa [majoritySetupMemory, Has, SlotMemory.write] using old 9 _ entryReady.Q
    all_goals
      apply get _ (by decide) (by decide)
      simp [majoritySetupMemory, Has, SlotMemory.write]
  obtain ⟨setupTrace, setupHead, setupLast, setupChain, setupLength, setupBounds, _⟩ := setupSegment.witness
  let later := joinTrace setupTrace loopTrace
  have laterHead := joinTrace_head setupTrace loopTrace entry loopState setupHead setupLast loopHead
  have laterLast := joinTrace_last setupTrace loopTrace after loopLast
  have laterChain := joinTrace_chain program (rawInput P fee) setupTrace loopTrace loopState
    setupChain loopChain setupLast loopHead
  have laterBounds : ∀ state ∈ later, StateBounds 64 (operandBudget P fee) state := by
    intro state member
    rcases List.mem_append.mp member with early | late
    · exact setupBounds state (List.mem_of_mem_dropLast early)
    · exact loopBounds state late
  refine ⟨after, joinTrace entryTrace later, endpoint,
    afterOutput.trans (setupSegment.output.trans entryOutput),
    joinTrace_head entryTrace later initial entry entryHead entryLast laterHead,
    joinTrace_last entryTrace later after laterLast,
    joinTrace_chain program (rawInput P fee) entryTrace later entry entryChain laterChain entryLast laterHead,
    ?_, ?_⟩
  · simp only [joinTrace, later, List.length_append, List.length_dropLast, entryLength]
    omega
  · intro state member
    rcases List.mem_append.mp member with early | late
    · exact entryBounds state (List.mem_of_mem_dropLast early)
    · exact laterBounds state late

end PDROC.D27Prepare.Search
