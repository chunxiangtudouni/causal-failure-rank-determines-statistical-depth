module

public import Paid.PDCompute_SolverEntryLoader_090
public import Paid.PDCompute_SolverZeroBadRuntime_083

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def goodEntryObjectiveCode : List Instruction := loadDenseEntryCode 35 7++headerCode goodObjectiveCommands

theorem goodEntryObjective_trace_memory (program : Program) (input : List Cell) (before : State)
    (base pointer n k : ℕ) (values : ℕ → Cell) (entry : MenuEntry) (fee penalty : ℚ)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpointer : values 35=.natural pointer) (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (source : PDLower.CalibrationCompute.HeapList before pointer (denseEncodeEntry entry))
    (outside : ∀ offset < 6,pointer+offset < base ∨ base+headerWords ≤ pointer+offset)
    (fetch : FetchesCode program before.pc goodEntryObjectiveCode) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 1530 ∧
      Header after base (goodObjectiveValues (denseReadHeaderValues (denseEncodeEntry entry) 7 values)
        fee penalty entry.observation entry.repairs entry.failure) ∧
      after.heap (base+21)=.rational (entry.objective fee penalty) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+goodEntryObjectiveCode.length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let loadedValues:=denseReadHeaderValues (denseEncodeEntry entry) 7 values
  have fetchLoad : FetchesCode program before.pc (loadDenseEntryCode 35 7) := fetch.append_left
  obtain ⟨loadTrace,loaded,loadHead,loadLast,loadChain,loadTime,loadedHeader,loadedBase,loadedPointer,loadedPC,loadFrame,loadOutput,loadMemory⟩ :=
    loadDenseEntry_trace_memory program input before base 35 7 pointer n k values entry header hbase (by decide) (by decide)
      hpointer source outside fetchLoad
  have hfee' : loadedValues 5=.rational fee :=
    (denseReadHeaderValues_preserves (denseEncodeEntry entry) 7 5 values (Or.inl (by decide))).trans hfee
  have hpenalty' : loadedValues 2=.rational penalty :=
    (denseReadHeaderValues_preserves (denseEncodeEntry entry) 7 2 values (Or.inl (by decide))).trans hpenalty
  have stats:=denseReadHeaderValues_good_stats entry values
  have fetchObjective : FetchesCode program loaded.pc (headerCode goodObjectiveCommands) := by
    rw [loadedPC]
    exact fetch.append_right
  obtain ⟨objectiveTrace,after,objectiveHead,objectiveLast,objectiveChain,objectiveTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,objectiveMemory⟩ :=
    goodObjective_trace_memory program input loaded base n k loadedValues fee penalty entry loadedHeader loadedBase
      hfee' hpenalty' stats.1 stats.2.1 stats.2.2 fetchObjective
  have joined:=joinTrace_spec program input loadTrace objectiveTrace before loaded after 705 825
    loadHead loadLast objectiveHead objectiveLast loadChain objectiveChain loadTime objectiveTime
  refine ⟨joinTrace loadTrace objectiveTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,
    (afterHeader.value 21 (by decide)).trans (goodObjectiveValues_objective loadedValues fee penalty entry),
    afterBase,?_,loadFrame.trans afterFrame,afterOutput.trans loadOutput,
    joinTrace_memory loadTrace objectiveTrace before loaded base loadLast loadMemory objectiveMemory⟩
  rw [afterPC,loadedPC,goodEntryObjectiveCode,List.length_append,loadDenseEntryCode_length]
  exact Nat.add_assoc _ _ _

end PDCompute.Solver
