module
public import Paid.PDCompute_Pack_EntryIteration_047

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation  PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

theorem localRegion_outside_dense (base source count pointer written : ℕ)
    (sourceLower : base+headerWords ≤ source) (sourceUpper : source+count ≤ pointer)
    (offset : ℕ) (inside : offset<count) : source+offset∉localRegion base pointer written := by
  intro member
  rcases Finset.mem_union.mp member with header|output
  · rw [headerRegion_eq,mem_cellRegion_iff] at header
    omega
  · rw [mem_cellRegion_iff] at output
    omega

theorem localRegion_outside_earlier (base pointer first later : ℕ)
    (lower : base+headerWords ≤ pointer) (offset : ℕ) (inside : offset<first) :
    pointer+offset∉localRegion base (pointer+first) later := by
  intro member
  rcases Finset.mem_union.mp member with header|output
  · rw [headerRegion_eq,mem_cellRegion_iff] at header
    omega
  · rw [mem_cellRegion_iff] at output
    omega

/-- Actual inner loop over all remaining columns. Every step is from
the fixed literal serializer. The dense input and the4/6 output are
independently defined; no serialized answer or whole-run premise enters. -/
theorem columns_trace (program : Program) (input : List Cell) (origin : ℕ) (entries : List MenuEntry)
    (before : State) (base source pointer n k : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+85)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : values sourceCursor=.natural source) (hpointer : values outputCursor=.natural pointer)
    (hcount : values columnRemaining=.natural entries.length)
    (dense : HeapList before source (denseEntries entries))
    (sourceLower : base+headerWords ≤ source)
    (sourceUpper : source+6*entries.length ≤ resultBase base n k)
    (pointerLower : resultBase base n k ≤ pointer) :
    ∃ trace : List State,∃ after : State,∃ finalValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 1830*entries.length+75 ∧
      Header after base finalValues ∧ HeapList after pointer (encodedEntries entries) ∧
      finalValues sourceCursor=.natural (source+6*entries.length) ∧
      finalValues outputCursor=.natural (pointer+(encodedEntries entries).length) ∧
      finalValues columnRemaining=.natural 0 ∧
      (∀ slot,entryStable slot → finalValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+213 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (localRegion base pointer (encodedEntries entries).length) := by
  induction entries generalizing before source pointer values with
  | nil=>
    have testFetch : FetchesCode program before.pc (counterTestCode columnRemaining (origin+213) (origin+89)) := by
      rw [pc]
      exact fetch_columnTest program origin code
    obtain ⟨trace,hh,hl,hchain,ht,afterHeader,afterBase,afterOutput,memory⟩:=
      counterTest_trace program input before base columnRemaining 0 (origin+213) (origin+89) values header
        (by decide) hbase hcount testFetch
    let after:=counterTestResult before base columnRemaining 0 (origin+213) (origin+89)
    refine ⟨trace,after,values,hh,hl,hchain,ht,afterHeader,?_,?_,?_,hcount,?_,afterBase,rfl,afterOutput,?_⟩
    · apply HeapList.of_values <;> intro offset bound <;> simp [encodedEntries] at bound
    · simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero] using hsource
    · simpa only [encodedEntries,List.flatMap_nil,List.length_nil,Nat.add_zero] using hpointer
    · intro slot _stable;rfl
    · intro state member
      exact headerMemory_local base pointer _ (memory state member)
  | cons entry entries ih=>
    have denseSplit : denseEntries (entry::entries)=denseEncodeEntry entry++denseEntries entries := by
      unfold denseEntries
      exact List.flatMap_cons
    have denseCombined : HeapList before source (denseEncodeEntry entry++denseEntries entries):=by rw [←denseSplit];exact dense
    have encodeSplit : encodedEntries (entry::entries)=encodeEntry entry++encodedEntries entries := by
      unfold encodedEntries
      exact List.flatMap_cons
    have payloadLength : (encodedEntries (entry::entries)).length=(encodeEntry entry).length+(encodedEntries entries).length := by
      rw [encodeSplit,List.length_append]
    have entryDense : HeapList before source (denseEncodeEntry entry):=denseCombined.append_left
    have sourceOutside : ∀ offset<6,source+offset<base ∨ base+headerWords ≤ source+offset:=by
      intro offset _bound;exact Or.inr (by omega)
    have targetLower : base+headerWords ≤ pointer:=(result_after_header base n k).trans pointerLower
    have targetOutside : ∀ offset<6,pointer+offset<base ∨ base+headerWords ≤ pointer+offset:=by
      intro offset _bound;exact Or.inr (by omega)
    obtain ⟨entryTrace,middle,entryHead,entryLast,entryChain,entryTime,middleHeader,entryHeap,middleBase,middlePC,middleOutput,entryMemory⟩:=
      entryIteration_trace program input origin before base source pointer (entry::entries).length n k entry values
        code pc header hbase hsource hpointer hcount (by simp) entryDense sourceOutside targetOutside
    let middleValues:=entryStepValues entry values source pointer (entry::entries).length
    have middleSource : middleValues sourceCursor=.natural (source+6):=entryStep_source entry values source pointer _
    have middlePointer : middleValues outputCursor=.natural (pointer+(encodeEntry entry).length):=entryStep_pointer entry values source pointer _
    have middleCount : middleValues columnRemaining=.natural entries.length := by
      dsimp only [middleValues]
      simpa only [List.length_cons,Nat.add_sub_cancel] using entryStep_count entry values source pointer (entry::entries).length
    have tailBefore : HeapList before (source+6) (denseEntries entries) := by
      have tail : HeapList before (source+(denseEncodeEntry entry).length) (denseEntries entries):=denseCombined.append_right
      simpa only [denseEncodeEntry_length,entryWords] using tail
    have middleMemory:=RegionMemory.trace_last entryMemory entryLast
    have tailDense : HeapList middle (source+6) (denseEntries entries):=tailBefore.regionMemory middleMemory (by
      intro offset bound
      apply localRegion_outside_dense base (source+6) (denseEntries entries).length pointer (encodeEntry entry).length
      · omega
      · rw [denseEntries_length]
        simp only [List.length_cons] at sourceUpper
        omega
      · exact bound)
    obtain ⟨tailTrace,after,finalValues,tailHead,tailLast,tailChain,tailTime,afterHeader,tailHeap,finalSource,finalPointer,finalCount,finalStable,afterBase,afterPC,afterOutput,tailMemory⟩:=
      ih middle (source+6) (pointer+(encodeEntry entry).length) middleValues middlePC middleHeader middleBase
        middleSource middlePointer middleCount tailDense (by omega)
        (by simp only [List.length_cons] at sourceUpper;omega) (by omega)
    have tailFinal:=RegionMemory.trace_last tailMemory tailLast
    have firstHeap : HeapList after pointer (encodeEntry entry):=entryHeap.regionMemory tailFinal (by
      intro offset bound
      exact localRegion_outside_earlier base pointer (encodeEntry entry).length (encodedEntries entries).length targetLower offset bound)
    have totalHeap : HeapList after pointer (encodedEntries (entry::entries)):=by
      rw [encodeSplit]
      exact firstHeap.append tailHeap
    have firstRegion : ∀ state∈entryTrace,RegionMemory before state
        (localRegion base pointer ((encodeEntry entry).length+(encodedEntries entries).length)):=
      fun state member=>(entryMemory state member).enlarge (localRegion_left_subset base pointer _ _)
    have tailRegion : ∀ state∈tailTrace,RegionMemory middle state
        (localRegion base pointer ((encodeEntry entry).length+(encodedEntries entries).length)):=
      fun state member=>(tailMemory state member).enlarge (localRegion_right_subset base pointer _ _)
    have joined:=joinTrace_spec program input entryTrace tailTrace before middle after 1830 (1830*entries.length+75)
      entryHead entryLast tailHead tailLast entryChain tailChain entryTime tailTime
    refine ⟨joinTrace entryTrace tailTrace,after,finalValues,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,totalHeap,
      ?_,?_,finalCount,?_,afterBase,afterPC,afterOutput.trans middleOutput,?_⟩
    · have bound:=joined.2.2.2
      simp only [List.length_cons]
      omega
    · rw [finalSource]
      congr 1
      simp only [List.length_cons]
      omega
    · rw [payloadLength]
      simpa only [Nat.add_assoc] using finalPointer
    · intro slot stable
      exact (finalStable slot stable).trans (entryStep_stable entry values source pointer _ slot stable)
    · rw [payloadLength]
      exact RegionMemory.join_trace entryTrace tailTrace before middle _ entryLast firstRegion tailRegion

end PDCompute.Pack
