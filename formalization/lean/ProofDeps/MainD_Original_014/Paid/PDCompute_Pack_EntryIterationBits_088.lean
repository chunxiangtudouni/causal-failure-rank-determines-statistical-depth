module
public import Paid.PDCompute_Pack_EntryEmissionBits_082
public import Paid.PDCompute_Pack_CounterTestBits_084
public import Paid.PDCompute_Pack_EntryAdvanceBits_087
public import Paid.PDCompute_Pack_EntryIteration_047

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

theorem entryIteration_trace_safe (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base source pointer count n k budget : ℕ) (entry : MenuEntry) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+85)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : values sourceCursor=.natural source) (hpointer : values outputCursor=.natural pointer)
    (hcount : values columnRemaining=.natural count) (positive : 0<count)
    (dense : HeapList before source (denseEncodeEntry entry))
    (sourceOutside : ∀ offset<6,source+offset<base ∨ base+headerWords ≤ source+offset)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (sourceBits : 1+natBits (source+6) ≤ budget) (twoBits : 1+natBits 2 ≤ budget)
    (pointerBits : 1+natBits (pointer+(encodeEntry entry).length) ≤ budget)
    (pcBits : ∀ counter ≤ origin+233,natBits counter ≤ budget)
    (targetOutside : ∀ offset<6,pointer+offset<base ∨ base+headerWords ≤ pointer+offset) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 1830 ∧
      Header after base (entryStepValues entry values source pointer count) ∧
      HeapList after pointer (encodeEntry entry) ∧ after.register .fresh=.natural base ∧
      after.pc=origin+85 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (localRegion base pointer (encodeEntry entry).length)) ∧ (∀ state∈trace,SafeBits state budget) := by
  have testFetch : FetchesCode program before.pc (counterTestCode columnRemaining (origin+213) (origin+89)) := by
    rw [pc]
    exact fetch_columnTest program origin code
  obtain ⟨testTrace,testHead,testLast,testChain,testTime,testHeader,testBase,testOutput,testMemory,testBits⟩:=
    counterTest_trace_safe program input before base columnRemaining count (origin+213) (origin+89) budget values header
      (by decide) hbase hcount safe (addressBits columnRemaining (by decide))
      (pcBits _ (by omega)) (pcBits _ (by omega)) (pcBits _ (by omega)) testFetch
  let tested:=counterTestResult before base columnRemaining count (origin+213) (origin+89)
  have testPC : tested.pc=origin+89 := by simp only [tested,counterTestResult,ite_eq_right (by omega : count≠0)]
  have testedSafe : SafeBits tested budget:=testBits tested (List.mem_of_getLast? testLast)
  obtain ⟨emitTrace,written,emitHead,emitLast,emitChain,emitTime,writtenHeader,heap,writtenBase,writtenPointer,writtenPC,writtenOutput,emitMemory,emitBits⟩:=
    entryEmissionLocal_trace_safe program input origin tested base source pointer n k budget entry values code testPC testHeader
      testBase hsource hpointer dense sourceOutside testedSafe addressBits sourceBits twoBits pointerBits pcBits targetOutside
  have writtenCount : entryValues entry values source columnRemaining=.natural count := by
    rw [entryValues_preserves entry values source columnRemaining (Or.inr (by decide)) (by decide)]
    exact hcount
  have writtenSafe : SafeBits written budget:=emitBits written (List.mem_of_getLast? emitLast)
  have oneBits : 1+natBits 1 ≤ budget:=(Nat.add_le_add_left (natBits_mono (by decide : 1 ≤ 2)) 1).trans twoBits
  obtain ⟨advanceTrace,after,advanceHead,advanceLast,advanceChain,advanceTime,afterHeader,afterBase,afterPC,afterOutput,advanceMemory,advanceBits⟩:=
    entryAdvance_trace_safe program input origin written base (pointer+(encodeEntry entry).length) count budget _ code writtenPC writtenHeader
      writtenBase writtenPointer writtenCount writtenSafe addressBits oneBits pcBits
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
      (RegionMemory.join_trace testTrace emitTrace before tested _ testLast testRegion emitMemory) advanceRegion,
    joinTrace_invariant (joinTrace testTrace emitTrace) advanceTrace (fun state=>SafeBits state budget)
      (joinTrace_invariant testTrace emitTrace (fun state=>SafeBits state budget) testBits emitBits) advanceBits⟩


end PDCompute.Pack
