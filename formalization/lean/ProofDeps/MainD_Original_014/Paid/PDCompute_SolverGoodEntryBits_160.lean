module

public import Paid.PDCompute_SolverEntryLoadBits_159
public import Paid.PDCompute_SolverObjectiveBits_157
public import Paid.PDCompute_SolverGoodBranchRuntime_091

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Whole ORIGINAL091 preceding-entry load and objective, real79-op
program with fine original entry bounds and SAME complete-state budget. -/
theorem goodEntryObjective_trace_bits (program : Program) (input : List Cell) (before : State)
    (base pointer n k budget S L T : ℕ) (values : ℕ → Cell) (entry : MenuEntry) (fee penalty : ℚ)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hpointer : values 35=.natural pointer) (hfee : values 5=.rational fee) (hpenalty : values 2=.rational penalty)
    (source : PDLower.CalibrationCompute.HeapList before pointer (denseEncodeEntry entry))
    (outside : ∀ offset<6,pointer+offset<base ∨ base+headerWords≤pointer+offset)
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pointerBits : 1+natBits (pointer+6)≤budget) (pcBits : natBits (before.pc+79)≤budget)
    (observation : ratEncodingBits entry.observation≤S) (repairs : ratEncodingBits entry.repairs≤S) (failure : ratEncodingBits entry.failure≤S)
    (feeBits : ratEncodingBits fee≤L) (penaltyBits : ratEncodingBits penalty≤T) (room : 1+16*(S+L+T+1)≤budget)
    (fetch : FetchesCode program before.pc goodEntryObjectiveCode) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤1530 ∧
      Header after base (goodObjectiveValues (denseReadHeaderValues (denseEncodeEntry entry) 7 values)
        fee penalty entry.observation entry.repairs entry.failure) ∧
      after.heap (base+21)=.rational (entry.objective fee penalty) ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+79 ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let loadedValues:=denseReadHeaderValues (denseEncodeEntry entry) 7 values
  obtain ⟨loadTrace,loaded,loadHead,loadLast,loadChain,loadTime,loadedHeader,loadedBase,_,loadedPC,loadFrame,loadOutput,loadMemory,loadSafe⟩:=
    loadDenseEntry_trace_bits program input before base 35 7 pointer n k budget values entry header fresh (by decide) (by decide) hpointer source outside safe
      addressBits pointerBits ((natBits_mono (by omega : before.pc+39≤before.pc+79)).trans pcBits) fetch.append_left
  have loadedFee : loadedValues 5=.rational fee :=
    (denseReadHeaderValues_preserves (denseEncodeEntry entry) 7 5 values (Or.inl (by decide))).trans hfee
  have loadedPenalty : loadedValues 2=.rational penalty :=
    (denseReadHeaderValues_preserves (denseEncodeEntry entry) 7 2 values (Or.inl (by decide))).trans hpenalty
  have stats:=denseReadHeaderValues_good_stats entry values
  have loadedBound:=loadSafe loaded (List.mem_of_getLast? loadLast)
  have objectivePC : natBits (loaded.pc+40)≤budget := by rw [loadedPC]; simpa only [Nat.add_assoc] using pcBits
  have objectiveFetch : FetchesCode program loaded.pc (headerCode goodObjectiveCommands) := by
    rw [loadedPC]
    simpa only [loadDenseEntryCode_length] using fetch.append_right
  obtain ⟨objectiveTrace,after,objectiveHead,objectiveLast,objectiveChain,objectiveTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,objectiveResources⟩:=
    goodObjective_trace_bits program input loaded base n k budget S L T loadedValues fee penalty entry loadedHeader loadedBase loadedBound
      loadedFee loadedPenalty stats.1 stats.2.1 stats.2.2 observation repairs failure feeBits penaltyBits room addressBits objectivePC objectiveFetch
  have joined:=joinTrace_spec program input loadTrace objectiveTrace before loaded after 705 825 loadHead loadLast objectiveHead objectiveLast
    loadChain objectiveChain loadTime objectiveTime
  refine ⟨joinTrace loadTrace objectiveTrace,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,afterHeader,
    (afterHeader.value 21 (by decide)).trans (goodObjectiveValues_objective loadedValues fee penalty entry),afterBase,?_,
    loadFrame.trans afterFrame,afterOutput.trans loadOutput,
    joinTrace_memory loadTrace objectiveTrace before loaded base loadLast loadMemory (fun state member=>(objectiveResources state member).1),
    PDCompute.Pack.joinTrace_invariant loadTrace objectiveTrace (fun state=>RootD27.Bits.SafeBits state budget) loadSafe
      (fun state member=>(objectiveResources state member).2)⟩
  rw [afterPC,loadedPC]

end PDCompute.Solver
