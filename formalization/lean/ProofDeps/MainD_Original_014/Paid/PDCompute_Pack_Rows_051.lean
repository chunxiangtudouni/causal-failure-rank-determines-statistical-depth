module
public import Paid.PDCompute_Pack_RowIteration_050

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation  PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- All remaining actual rows of the fixed literal program, including
the final zero guard that transfers control to the real return block. -/
theorem rows_trace (program : Program) (input : List Cell) (origin : ℕ) (rows : List MenuRow)
    (before : State) (base source pointer columns n k : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+63)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : values sourceCursor=.natural source) (hpointer : values outputCursor=.natural pointer)
    (hcount : values rowRemaining=.natural rows.length) (hcolumns : values columnsPerRow=.natural columns)
    (width : ∀ row∈rows,row.size=columns)
    (dense : HeapList before source (denseRows rows))
    (sourceLower : base+headerWords ≤ source)
    (sourceUpper : source+6*rows.length*columns ≤ resultBase base n k)
    (pointerLower : resultBase base n k ≤ pointer) :
    ∃ trace : List State,∃ after : State,∃ finalValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace ≤ rows.length*(1830*columns+645)+75 ∧
      Header after base finalValues ∧ HeapList after pointer (encodedRows rows) ∧
      finalValues sourceCursor=.natural (source+6*rows.length*columns) ∧
      finalValues outputCursor=.natural (pointer+(encodedRows rows).length) ∧
      finalValues rowRemaining=.natural 0 ∧
      (∀ slot,tableStable slot → finalValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+222 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (localRegion base pointer (encodedRows rows).length) := by
  induction rows generalizing before source pointer values with
  | nil=>
    simp only [List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.mul_zero,Nat.add_zero]
    have guardFetch : FetchesCode program before.pc (counterTestCode rowRemaining (origin+222) (origin+67)) := by
      rw [pc]
      exact fetch_rowTest program origin code
    obtain ⟨trace,hh,hl,hchain,ht,afterHeader,afterBase,afterOutput,memory⟩:=
      counterTest_trace program input before base rowRemaining 0 (origin+222) (origin+67) values header (by decide) hbase hcount guardFetch
    let after:=counterTestResult before base rowRemaining 0 (origin+222) (origin+67)
    refine ⟨trace,after,values,hh,hl,hchain,ht,afterHeader,?_,?_,?_,hcount,?_,afterBase,rfl,afterOutput,?_⟩
    · apply HeapList.of_values <;> intro offset bound <;> simp [encodedRows] at bound
    · exact hsource
    · simpa only [encodedRows,List.flatMap_nil,List.length_nil,Nat.add_zero] using hpointer
    · intro slot _stable;rfl
    · intro state member
      exact headerMemory_local base pointer _ (memory state member)
  | cons row rows ih=>
    have denseSplit : denseRows (row::rows)=denseEntries row.toList++denseRows rows := by
      unfold denseRows
      exact List.flatMap_cons
    have denseCombined : HeapList before source (denseEntries row.toList++denseRows rows):=by rw [←denseSplit];exact dense
    have encodeSplit : encodedRows (row::rows)=encodeRow row++encodedRows rows := by
      unfold encodedRows
      exact List.flatMap_cons
    have payloadLength : (encodedRows (row::rows)).length=(encodeRow row).length+(encodedRows rows).length := by
      rw [encodeSplit,List.length_append]
    have currentWidth:=width row (by simp)
    have tailWidth : ∀ row∈rows,row.size=columns:=fun row member=>width row (by simp [member])
    have rowDense : HeapList before source (denseEntries row.toList):=denseCombined.append_left
    have expandedUpper : source+6*columns+6*rows.length*columns ≤ resultBase base n k := by
      have expanded:=sourceUpper
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_mul] at expanded
      omega
    obtain ⟨rowTrace,middle,middleValues,rowHead,rowLast,rowChain,rowTime,middleHeader,rowHeap,middleSource,middlePointer,middleCount,middleStable,middleBase,middlePC,middleOutput,rowMemory⟩:=
      rowIteration_trace program input origin row before base source pointer (row::rows).length n k values
        code pc header hbase hsource hpointer hcount (by simp) (by rw [currentWidth];exact hcolumns)
        rowDense sourceLower (by rw [currentWidth];omega) pointerLower
    have nextSource : middleValues sourceCursor=.natural (source+6*columns) := by simpa only [currentWidth] using middleSource
    have nextCount : middleValues rowRemaining=.natural rows.length := by
      simpa only [List.length_cons,Nat.add_sub_cancel] using middleCount
    have nextColumns : middleValues columnsPerRow=.natural columns :=
      (middleStable columnsPerRow columnsPerRow_tableStable).trans hcolumns
    have tailBefore : HeapList before (source+6*columns) (denseRows rows) := by
      have tail : HeapList before (source+(denseEntries row.toList).length) (denseRows rows):=denseCombined.append_right
      simpa only [denseEntries_length,Array.length_toList,currentWidth] using tail
    have middleMemory:=RegionMemory.trace_last rowMemory rowLast
    have tailDense : HeapList middle (source+6*columns) (denseRows rows):=tailBefore.regionMemory middleMemory (by
      intro offset bound
      apply localRegion_outside_dense base (source+6*columns) (denseRows rows).length pointer (encodeRow row).length
      · omega
      · rw [denseRows_length rows columns tailWidth]
        omega
      · exact bound)
    obtain ⟨tailTrace,after,finalValues,tailHead,tailLast,tailChain,tailTime,afterHeader,tailHeap,finalSource,finalPointer,finalCount,finalStable,afterBase,afterPC,afterOutput,tailMemory⟩:=
      ih middle (source+6*columns) (pointer+(encodeRow row).length) middleValues middlePC middleHeader middleBase
        nextSource middlePointer nextCount nextColumns tailWidth tailDense (by omega) (by omega) (by omega)
    have tailFinal:=RegionMemory.trace_last tailMemory tailLast
    have firstHeap : HeapList after pointer (encodeRow row):=rowHeap.regionMemory tailFinal (by
      intro offset bound
      exact localRegion_outside_earlier base pointer (encodeRow row).length (encodedRows rows).length
        ((result_after_header base n k).trans pointerLower) offset bound)
    have totalHeap : HeapList after pointer (encodedRows (row::rows)):=by
      rw [encodeSplit]
      exact firstHeap.append tailHeap
    have firstRegion : ∀ state∈rowTrace,RegionMemory before state
        (localRegion base pointer ((encodeRow row).length+(encodedRows rows).length)):=
      fun state member=>(rowMemory state member).enlarge (localRegion_left_subset base pointer _ _)
    have tailRegion : ∀ state∈tailTrace,RegionMemory middle state
        (localRegion base pointer ((encodeRow row).length+(encodedRows rows).length)):=
      fun state member=>(tailMemory state member).enlarge (localRegion_right_subset base pointer _ _)
    have joined:=joinTrace_spec program input rowTrace tailTrace before middle after (1830*columns+645) (rows.length*(1830*columns+645)+75)
      rowHead rowLast tailHead tailLast rowChain tailChain (by simpa only [currentWidth] using rowTime) tailTime
    refine ⟨joinTrace rowTrace tailTrace,after,finalValues,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,totalHeap,
      ?_,?_,finalCount,?_,afterBase,afterPC,afterOutput.trans middleOutput,?_⟩
    · calc
        time program (joinTrace rowTrace tailTrace) ≤ (1830*columns+645)+(rows.length*(1830*columns+645)+75):=joined.2.2.2
        _=(row::rows).length*(1830*columns+645)+75:=by
          rw [List.length_cons,Nat.add_mul,Nat.one_mul]
          ac_rfl
    · rw [finalSource]
      congr 1
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_mul]
      omega
    · rw [payloadLength]
      simpa only [Nat.add_assoc] using finalPointer
    · intro slot stable
      exact (finalStable slot stable).trans (middleStable slot stable)
    · rw [payloadLength]
      exact RegionMemory.join_trace rowTrace tailTrace before middle _ rowLast firstRegion tailRegion

end PDCompute.Pack
