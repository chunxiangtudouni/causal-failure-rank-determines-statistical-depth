module
public import Paid.PDCompute_Pack_EntryLocal_045
public import Paid.PDCompute_Pack_Sequence_046
public import Paid.PDCompute_Pack_CounterTest_038
public import Paid.PDCompute_Pack_WordStream_040

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation  PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- One actual nonempty column iteration, including guard, real dense
read, true4/6 output writes, counter decrement, and back-edge. -/
theorem entryIteration_trace (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base source pointer count n k : ℕ) (entry : MenuEntry) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+85)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : values sourceCursor=.natural source) (hpointer : values outputCursor=.natural pointer)
    (hcount : values columnRemaining=.natural count) (positive : 0<count)
    (dense : HeapList before source (denseEncodeEntry entry))
    (sourceOutside : ∀ offset<6,source+offset<base ∨ base+headerWords ≤ source+offset)
    (targetOutside : ∀ offset<6,pointer+offset<base ∨ base+headerWords ≤ pointer+offset) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 1830 ∧
      Header after base (entryStepValues entry values source pointer count) ∧
      HeapList after pointer (encodeEntry entry) ∧ after.register .fresh=.natural base ∧
      after.pc=origin+85 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (localRegion base pointer (encodeEntry entry).length) := by
  have testFetch : FetchesCode program before.pc (counterTestCode columnRemaining (origin+213) (origin+89)) := by
    rw [pc]
    exact fetch_columnTest program origin code
  obtain ⟨testTrace,testHead,testLast,testChain,testTime,testHeader,testBase,testOutput,testMemory⟩:=
    counterTest_trace program input before base columnRemaining count (origin+213) (origin+89) values header
      (by decide) hbase hcount testFetch
  let tested:=counterTestResult before base columnRemaining count (origin+213) (origin+89)
  have testPC : tested.pc=origin+89 := by simp only [tested,counterTestResult,ite_eq_right (by omega : count≠0)]
  obtain ⟨emitTrace,written,emitHead,emitLast,emitChain,emitTime,writtenHeader,heap,writtenBase,writtenPointer,writtenPC,writtenOutput,emitMemory⟩:=
    entryEmissionLocal_trace program input origin tested base source pointer n k entry values code testPC testHeader
      testBase hsource hpointer dense sourceOutside targetOutside
  have writtenCount : entryValues entry values source columnRemaining=.natural count := by
    rw [entryValues_preserves entry values source columnRemaining (Or.inr (by decide)) (by decide)]
    exact hcount
  obtain ⟨advanceTrace,after,advanceHead,advanceLast,advanceChain,advanceTime,afterHeader,afterBase,afterPC,afterOutput,advanceMemory⟩:=
    entryAdvance_trace program input origin written base (pointer+(encodeEntry entry).length) count _ code writtenPC writtenHeader
      writtenBase writtenPointer writtenCount
  have finalMemory:=HeaderMemory.trace_last advanceMemory advanceLast
  have finalHeap : HeapList after pointer (encodeEntry entry):=heap.headerMemory finalMemory
    (by intro offset bound;exact targetOutside offset (by have cap:=encodeEntry_length_le entry;omega))
  have testRegion : ∀ state∈testTrace,RegionMemory before state (localRegion base pointer (encodeEntry entry).length):=
    fun state member=>headerMemory_local base pointer (encodeEntry entry).length (testMemory state member)
  have advanceRegion : ∀ state∈advanceTrace,RegionMemory written state (localRegion base pointer (encodeEntry entry).length):=
    fun state member=>headerMemory_local base pointer (encodeEntry entry).length (advanceMemory state member)
  have firstJoin:=joinTrace_spec program input testTrace emitTrace before tested written 75 1545
    testHead testLast emitHead emitLast testChain emitChain testTime emitTime
  have lastJoin:=joinTrace_spec program input (joinTrace testTrace emitTrace) advanceTrace before written after 1620 210
    firstJoin.1 firstJoin.2.1 advanceHead advanceLast firstJoin.2.2.1 advanceChain firstJoin.2.2.2 advanceTime
  exact ⟨joinTrace (joinTrace testTrace emitTrace) advanceTrace,after,lastJoin.1,lastJoin.2.1,lastJoin.2.2.1,lastJoin.2.2.2,
    afterHeader,finalHeap,afterBase,afterPC,afterOutput.trans (writtenOutput.trans testOutput),
    RegionMemory.join_trace (joinTrace testTrace emitTrace) advanceTrace before written _ firstJoin.2.1
      (RegionMemory.join_trace testTrace emitTrace before tested _ testLast testRegion emitMemory) advanceRegion⟩

end PDCompute.Pack
