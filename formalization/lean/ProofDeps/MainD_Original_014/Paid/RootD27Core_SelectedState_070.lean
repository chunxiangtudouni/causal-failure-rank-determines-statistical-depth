module

public import Paid.RootD27Core_SelectedMetadata_069

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

theorem selectedMetadata_price (values : ℕ→Cell) (upper isExact : Bool) :
    selectedMetadataValues values upper isExact (multiplierSlot upper)=values 24 := by
  cases upper <;> simp [selectedMetadataValues,multiplierSlot,statisticsSlot]

theorem selectedMetadata_statistics (values : ℕ→Cell) (upper isExact : Bool) (offset : ℕ)
    (inside : offset<3) :
    selectedMetadataValues values upper isExact (statisticsSlot upper+offset)=values (25+offset) := by
  interval_cases offset <;> cases upper <;> simp [selectedMetadataValues,multiplierSlot,statisticsSlot]

theorem selectedMetadata_tag (values : ℕ→Cell) (upper isExact : Bool) :
    selectedMetadataValues values upper isExact 13=.natural (if isExact then 0 else 1) := by
  simp only [selectedMetadataValues,Function.update_self]

theorem selectedMetadata_bound (upper : Bool) (address : ℕ) (member : address∈selectedMetadataRegion upper) :
    address≤21 := by
  cases upper <;> simp only [selectedMetadataRegion,multiplierSlot,statisticsSlot,
    Bool.false_eq_true,ite_false,ite_true,Finset.mem_insert,Finset.mem_singleton] at member <;> omega

theorem selectedMetadata_above_outside (upper : Bool) (address : ℕ) (above : 22≤address) :
    address∉selectedMetadataRegion upper := by
  intro member
  have bound:=selectedMetadata_bound upper address member
  omega

theorem selectedMetadata_other_price_outside (written kept : Bool) (different : written≠kept) :
    multiplierSlot kept∉selectedMetadataRegion written := by
  cases written <;> cases kept <;> simp_all [selectedMetadataRegion,multiplierSlot,statisticsSlot]

theorem selectedMetadata_other_statistics_outside (written kept : Bool) (different : written≠kept)
    (offset : ℕ) (inside : offset<3) : statisticsSlot kept+offset∉selectedMetadataRegion written := by
  cases written <;> cases kept <;> simp_all [selectedMetadataRegion,statisticsSlot,multiplierSlot] <;> omega

theorem header_scalarHeapList {state : State} {values : ℕ→Cell} (header : Header state 0 values)
    (slot : ℕ) (cells : List Cell) (bounded : slot+cells.length≤headerWords)
    (payload : ∀ offset (inside : offset<cells.length),values (slot+offset)=cells[offset]'inside) : HeapList state slot cells := by
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset inside
    have inHeader : slot+offset<headerWords:=by omega
    simpa only [Nat.zero_add] using header.live (slot+offset) inHeader
  · intro offset inside
    have inHeader : slot+offset<headerWords:=by omega
    have value:=header.value (slot+offset) inHeader
    simp only [Nat.zero_add] at value
    exact value.trans (payload offset inside)

theorem SolvedBuffer.preserve_selected_metadata {P : Parameters} {fee penalty : ℚ}
    {kept written : Bool} {before after : State} (represented : SolvedBuffer P fee penalty kept before)
    (different : written≠kept) (memory : RegionMemory before after (selectedMetadataRegion written)) :
    SolvedBuffer P fee penalty kept after := by
  have tableLower : 48≤retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools kept := by
    have lower:=retained_base_above_workspace (99+2*P.certificate.M) P.certificate.stages P.tools kept
    unfold workspaceSize headerWords at lower
    omega
  apply represented.preserve _ memory
  · intro offset inside
    have zero : offset=0:=by omega
    subst offset
    simpa only [Nat.add_zero] using selectedMetadata_other_price_outside written kept different
  · intro offset inside
    exact selectedMetadata_other_statistics_outside written kept different offset inside
  · intro offset _inside
    apply selectedMetadata_above_outside
    have lower : 22≤tableLengthSlot kept:=by cases kept <;> decide
    omega
  · intro offset _inside
    apply selectedMetadata_above_outside
    omega

/-- Given the table/length actually copied by068 and the real midpoint
fields24..27, execute the selected28-op metadata writer. The output is a
complete physical solved buffer and a physically stored source tag.
These are internal run-produced inputs, not original caller promises. -/
theorem selected_state_actual (P : Parameters) (fee penalty : ℚ) (program : Program) (input : List Cell)
    (before : State) (values : ℕ→Cell) (upper isExact : Bool) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0) (middlePrice : values 24=.rational penalty)
    (middleStatistics : HeapList before 25 (originalStatistics P fee penalty))
    (copiedTable : HeapList before
      (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper)
      (originalSolveEncoding P fee penalty))
    (copiedLength : HeapList before (tableLengthSlot upper) [.natural (originalSolveEncoding P fee penalty).length])
    (fetched : FetchesCode program before.pc (headerCode (selectedMetadataCommands upper isExact))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤435 ∧
      after.pc=before.pc+28 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ SolvedBuffer P fee penalty upper after ∧
      HeapList after 13 [.natural (if isExact then 0 else 1)] ∧
      RegionMemory before after (selectedMetadataRegion upper) ∧
      (∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+28) ∧
      peakCells trace≤workingCells before := by
  obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,pc,memory,prefixMemory,scope,peak⟩:=
    selected_metadata_actual program input before values upper isExact header fresh fetched
  have sourceValues : ∀ offset (inside : offset<3),values (25+offset)=(originalStatistics P fee penalty)[offset]'inside := by
    intro offset inside
    have bound : 25+offset<headerWords:=by unfold headerWords;omega
    have value:=header.value (25+offset) bound
    simp only [Nat.zero_add] at value
    exact value.symm.trans (PDLower.CalibrationCompute.HeapList.value middleStatistics offset inside)
  have priceAfter : HeapList after (multiplierSlot upper) [.rational penalty] := by
    apply header_scalarHeapList afterHeader
    · change multiplierSlot upper+1≤headerWords
      cases upper <;> decide
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      simpa only [Nat.add_zero,List.getElem_cons_zero] using
        (selectedMetadata_price values upper isExact).trans middlePrice
  have statisticsAfter : HeapList after (statisticsSlot upper) (originalStatistics P fee penalty) := by
    apply header_scalarHeapList afterHeader
    · change statisticsSlot upper+3≤headerWords
      cases upper <;> decide
    · intro offset inside
      change offset<3 at inside
      exact (selectedMetadata_statistics values upper isExact offset inside).trans (sourceValues offset inside)
  have lengthAfter : HeapList after (tableLengthSlot upper) [.natural (originalSolveEncoding P fee penalty).length] := by
    apply memory.heapList copiedLength
    intro offset _inside
    apply selectedMetadata_above_outside
    have lower : 22≤tableLengthSlot upper:=by cases upper <;> decide
    omega
  have tableAfter : HeapList after
      (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper)
      (originalSolveEncoding P fee penalty) := by
    apply memory.heapList copiedTable
    intro offset _inside
    apply selectedMetadata_above_outside
    have lower:=retained_base_above_workspace (99+2*P.certificate.M) P.certificate.stages P.tools upper
    unfold workspaceSize headerWords at lower
    omega
  have tagAfter : HeapList after 13 [.natural (if isExact then 0 else 1)] := by
    apply header_scalarHeapList afterHeader
    · change 13+1≤headerWords
      decide
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      simpa only [Nat.add_zero,List.getElem_cons_zero] using selectedMetadata_tag values upper isExact
  have liveHeader : Header after 0 (fun slot=>after.heap slot) := by
    intro slot inside
    exact ⟨afterHeader.live slot inside,by simp only [Nat.zero_add]⟩
  exact ⟨trace,after,head,last,chain,cost,pc,afterFresh,liveHeader,
    ⟨priceAfter,statisticsAfter,lengthAfter,tableAfter⟩,tagAfter,memory,prefixMemory,scope,peak⟩

end RootD27.Core
