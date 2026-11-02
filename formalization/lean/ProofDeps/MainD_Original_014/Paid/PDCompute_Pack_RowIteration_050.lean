module
public import Paid.PDCompute_Pack_RowModels_049
public import Paid.PDCompute_Pack_Columns_048

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation  PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- One actual complete row, including both loop tests, real row-length
store, all variable-width entry copies, and the real row back-edge. -/
theorem rowIteration_trace (program : Program) (input : List Cell) (origin : ℕ) (row : MenuRow)
    (before : State) (base source pointer count n k : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+63)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : values sourceCursor=.natural source) (hpointer : values outputCursor=.natural pointer)
    (hcount : values rowRemaining=.natural count) (positive : 0<count)
    (hcolumns : values columnsPerRow=.natural row.size)
    (dense : HeapList before source (denseEntries row.toList))
    (sourceLower : base+headerWords ≤ source)
    (sourceUpper : source+6*row.size ≤ resultBase base n k)
    (pointerLower : resultBase base n k ≤ pointer) :
    ∃ trace : List State,∃ after : State,∃ finalValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 1830*row.size+645 ∧
      Header after base finalValues ∧ HeapList after pointer (encodeRow row) ∧
      finalValues sourceCursor=.natural (source+6*row.size) ∧
      finalValues outputCursor=.natural (pointer+(encodeRow row).length) ∧
      finalValues rowRemaining=.natural (count-1) ∧
      (∀ slot,tableStable slot → finalValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+63 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (localRegion base pointer (encodeRow row).length) := by
  have guardFetch : FetchesCode program before.pc (counterTestCode rowRemaining (origin+222) (origin+67)) := by
    rw [pc]
    exact fetch_rowTest program origin code
  obtain ⟨guardTrace,guardHead,guardLast,guardChain,guardTime,guardHeader,guardBase,guardOutput,guardMemory⟩:=
    counterTest_trace program input before base rowRemaining count (origin+222) (origin+67) values header (by decide) hbase hcount guardFetch
  let tested:=counterTestResult before base rowRemaining count (origin+222) (origin+67)
  have testedPC : tested.pc=origin+67 := by simp only [tested,counterTestResult,ite_eq_right (by omega : count≠0)]
  have pointerOutside : base+headerWords ≤ pointer:=(result_after_header base n k).trans pointerLower
  obtain ⟨wordTrace,started,wordHead,wordLast,wordChain,wordTime,startedHeader,wordHeap,startedBase,startedPC,startedOutput,wordMemory⟩:=
    startRowLocal_trace program input origin tested base pointer values code testedPC guardHeader guardBase hpointer (Or.inr pointerOutside)
  let startedValues:=startRowValues values pointer
  have startedSource : startedValues sourceCursor=.natural source:=(startRowValues_source values pointer).trans hsource
  have startedPointer : startedValues outputCursor=.natural (pointer+1):=startRowValues_pointer values pointer
  have startedCount : startedValues columnRemaining=.natural row.toList.length := by
    simpa only [Array.length_toList] using (startRowValues_count values pointer).trans hcolumns
  have wordFinal:=RegionMemory.trace_last wordMemory wordLast
  have startedDense : HeapList started source (denseEntries row.toList):=dense.regionMemory wordFinal (by
    intro offset bound
    apply localRegion_outside_dense base source (denseEntries row.toList).length pointer 1 sourceLower
    · simpa only [denseEntries_length,Array.length_toList] using sourceUpper.trans pointerLower
    · exact bound)
  obtain ⟨columnsTrace,completed,columnValues,columnsHead,columnsLast,columnsChain,columnsTime,columnHeader,entryHeap,columnSource,columnPointer,columnCount,columnStable,columnBase,columnPC,columnOutput,columnMemory⟩:=
    columns_trace program input origin row.toList started base source (pointer+1) n k startedValues code startedPC
      startedHeader startedBase startedSource startedPointer startedCount startedDense sourceLower
      (by simpa only [Array.length_toList] using sourceUpper) (by omega)
  have completedCount : columnValues rowRemaining=.natural count :=
    (columnStable rowRemaining rowRemaining_entryStable).trans
      ((startRowValues_stable values pointer rowRemaining rowRemaining_entryStable).trans hcount)
  have backFetch : FetchesCode program completed.pc (counterBackCode rowRemaining (origin+63)) := by
    rw [columnPC]
    exact fetch_rowAdvance program origin code
  obtain ⟨backTrace,after,backHead,backLast,backChain,backTime,afterHeader,afterBase,afterPC,afterOutput,backMemory⟩:=
    counterBack_trace program input completed base rowRemaining count (origin+63) columnValues columnHeader
      (by decide) columnBase completedCount backFetch
  let finalValues:=Function.update columnValues rowRemaining (.natural (count-1))
  have columnsFinal:=RegionMemory.trace_last columnMemory columnsLast
  have keptWord : HeapList completed pointer [values columnsPerRow]:=wordHeap.regionMemory columnsFinal (by
    intro offset bound
    exact localRegion_outside_earlier base pointer 1 (encodedEntries row.toList).length pointerOutside offset bound)
  have rowHeap : HeapList completed pointer (encodeRow row) := by
    rw [encodeRow_eq]
    simpa only [hcolumns,List.singleton_append] using keptWord.append entryHeap
  have backFinal:=HeaderMemory.trace_last backMemory backLast
  have finalHeap : HeapList after pointer (encodeRow row):=rowHeap.headerMemory backFinal (by
    intro offset _bound;exact Or.inr (by omega))
  have rowLength : (encodeRow row).length=1+(encodedEntries row.toList).length := by rw [encodeRow_eq];simp only [List.length_cons];omega
  have guardRegion : ∀ state∈guardTrace,RegionMemory before state (localRegion base pointer (encodeRow row).length):=
    fun state member=>headerMemory_local base pointer _ (guardMemory state member)
  have wordRegion : ∀ state∈wordTrace,RegionMemory tested state (localRegion base pointer (encodeRow row).length) := by
    intro state member
    rw [rowLength]
    exact (wordMemory state member).enlarge (localRegion_left_subset base pointer 1 _)
  have columnRegion : ∀ state∈columnsTrace,RegionMemory started state (localRegion base pointer (encodeRow row).length) := by
    intro state member
    rw [rowLength]
    exact (columnMemory state member).enlarge (localRegion_right_subset base pointer 1 _)
  have backRegion : ∀ state∈backTrace,RegionMemory completed state (localRegion base pointer (encodeRow row).length):=
    fun state member=>headerMemory_local base pointer _ (backMemory state member)
  have firstJoin:=joinTrace_spec program input guardTrace wordTrace before tested started 75 345
    guardHead guardLast wordHead wordLast guardChain wordChain guardTime wordTime
  have secondJoin:=joinTrace_spec program input (joinTrace guardTrace wordTrace) columnsTrace before started completed 420 (1830*row.size+75)
    firstJoin.1 firstJoin.2.1 columnsHead columnsLast firstJoin.2.2.1 columnsChain firstJoin.2.2.2
    (by simpa only [Array.length_toList] using columnsTime)
  have finalJoin:=joinTrace_spec program input (joinTrace (joinTrace guardTrace wordTrace) columnsTrace) backTrace before completed after
    (1830*row.size+495) 150 secondJoin.1 secondJoin.2.1 backHead backLast secondJoin.2.2.1 backChain
    (by have bound:=secondJoin.2.2.2;omega) backTime
  refine ⟨joinTrace (joinTrace (joinTrace guardTrace wordTrace) columnsTrace) backTrace,after,finalValues,
    finalJoin.1,finalJoin.2.1,finalJoin.2.2.1,?_,afterHeader,finalHeap,?_,?_,Function.update_self _ _ _,?_,
    afterBase,afterPC,afterOutput.trans (columnOutput.trans (startedOutput.trans guardOutput)),?_⟩
  · have bound:=finalJoin.2.2.2;omega
  · unfold finalValues
    rw [Function.update_of_ne (by decide : sourceCursor≠rowRemaining)]
    simpa only [Array.length_toList] using columnSource
  · unfold finalValues
    rw [Function.update_of_ne (by decide : outputCursor≠rowRemaining),columnPointer,rowLength]
    congr 1
    omega
  · intro slot stable
    unfold finalValues
    rw [Function.update_of_ne stable.2]
    exact (columnStable slot stable.1).trans (startRowValues_stable values pointer slot stable.1)
  · exact RegionMemory.join_trace (joinTrace (joinTrace guardTrace wordTrace) columnsTrace) backTrace before completed _ secondJoin.2.1
      (RegionMemory.join_trace (joinTrace guardTrace wordTrace) columnsTrace before started _ firstJoin.2.1
        (RegionMemory.join_trace guardTrace wordTrace before tested _ guardLast guardRegion wordRegion) columnRegion) backRegion

end PDCompute.Pack
