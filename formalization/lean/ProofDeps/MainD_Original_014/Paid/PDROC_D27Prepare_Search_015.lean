module

public import Paid.PDROC_D27Prepare_Search_004
public import Paid.PDROC_D27Prepare_Memory_001
public import Paid.PDROC_D27Prepare_Resources_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Search

/-- The original six-cell input genuinely reaches the typed search
boundary. Every literal constant and scalar is read from the initialized
heap, and all actual input/prologue states have the uniform bit envelope.
No SearchInitial state or derived certificate is a caller premise. -/
theorem raw_initial_trace (P : Parameters) (fee : ℚ) :
    ∃ (after : State) (trace : List State), SearchInitial P fee after ∧
      after.output = [] ∧ trace.head? = some initial ∧ trace.getLast? = some after ∧
      trace.length = 89 ∧ trace.IsChain (fun a b => step program (rawInput P fee) a = some b) ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) := by
  obtain ⟨after, trace, matched, location, output, head, last, length, chain, _, bounds⟩ :=
    raw_bounded_prologue_trace P fee
  let memory := initializedInputMemory (.natural P.certificate.stages) (.natural P.tools)
    (.rational P.certificate.gamma) (.rational P.certificate.risk) (.rational P.reviewFee) (.rational fee)
  have actual (address : ℕ) (value : Cell) (stored : Has memory address value) :
      SlotHas after address value := match_has after memory address value matched stored
  have raw : RawConstants P fee after := by
    constructor
    · exact matched.base
    all_goals
      apply actual
      norm_num [Has, memory, initializedInputMemory, initializationResult, loadedInputMemory,
        emptySlotMemory, SlotMemory.write]
  have ready : SearchInitial P fee after := by
    refine ⟨raw, location, ?_, ?_, ?_, ?_⟩
    all_goals
      apply actual
      norm_num [Has, memory, initializedInputMemory, initializationResult, loadedInputMemory,
        emptySlotMemory, SlotMemory.write]
  exact ⟨after, trace, ready, output, head, last, length, chain, bounds⟩

end PDROC.D27Prepare.Search
