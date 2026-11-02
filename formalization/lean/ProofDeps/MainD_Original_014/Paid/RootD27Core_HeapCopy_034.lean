module

public import Paid.RootD27Core_HeapCopyStep_033
public import Paid.PDCompute_Pack_Sequence_046

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

theorem heapCopy_region_cells {before after : State} (target count : ℕ)
    (memory : RegionMemory before after (cellRegion target count)) :
    workingCells after≤workingCells before+count := by
  have card : (cellRegion target count).card≤count := by
    unfold cellRegion
    exact Finset.card_image_le.trans (by rw [Finset.card_range])
  exact memory.workingCells_le.trans (Nat.add_le_add_left card _)

theorem heapCopyNext_singleton (before : State) (source target remaining origin : ℕ) :
    PDLower.CalibrationCompute.HeapList (heapCopyNext before source target remaining origin)
      target [before.heap source] := by
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset bound
    have zero : offset=0 := by simp only [List.length_cons,List.length_nil] at bound;omega
    subst offset
    simp [heapCopyNext,heapCopyCellResult]
  · intro offset bound
    have zero : offset=0 := by simp only [List.length_cons,List.length_nil] at bound;omega
    subst offset
    simp [heapCopyNext,heapCopyCellResult]

/-- One fixed nine-instruction physical heap copier for arbitrary live
source lists, runtime lengths and disjoint runtime destinations. No
destination cells, copied answers or successful execution are supplied.
Every prefix retains old live cells/output and writes only the actual
destination interval. Source cells survive and the saved return is real. -/
theorem heapCopy_actual (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (before : State) (source target : ℕ) (cells : List Cell)
    (position : before.pc=origin) (address : before.register .address=.natural source)
    (fresh : before.register .fresh=.natural target) (index : before.register .index=.natural cells.length)
    (old : before.register .old=.natural returnPC) (stored : HeapList before source cells)
    (separate : source+cells.length≤target ∨ target+cells.length≤source)
    (fetched : FetchesCode program origin (heapCopyCode origin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤150*cells.length+45 ∧ after.pc=returnPC ∧
      after.register .fresh=.natural (target+cells.length) ∧
      after.register .address=.natural (source+cells.length) ∧
      after.register .index=.natural 0 ∧ after.register .old=.natural returnPC ∧
      HeapList after target cells ∧ HeapList after source cells ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+cells.length ∧
      (∀ state∈trace,RegionMemory before state (cellRegion target cells.length)) := by
  induction cells generalizing before source target with
  | nil =>
    obtain ⟨trace,head,last,chain,cost,memory⟩:=heapCopy_zero_actual program input origin returnPC before position index old fetched
    have allMemory:=memory (cellRegion target 0)
    have allSpace : ∀ state∈trace,workingCells state≤workingCells before+0 :=
      fun state member=>heapCopy_region_cells target 0 (allMemory state member)
    refine ⟨trace,{before with pc:=returnPC},head,last,chain,cost,rfl,fresh,address,index,old,?_,stored,rfl,
      PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory⟩
    simp [HeapList,heapSegment]
  | cons value cells ih =>
    have live : source∈before.live:=stored.1 0 (by simp)
    obtain ⟨first,fh,fl,fc,ft,fm⟩:=heapCopy_step_actual program input origin before source target cells.length
      position address fresh index live fetched
    let next:=heapCopyNext before source target cells.length origin
    have nextMemory : RegionMemory before next {target}:=RegionMemory.trace_last fm fl
    have sourceTail : HeapList before (source+1) cells :=
      PDLower.CalibrationCompute.HeapList.append_right (first:=[value]) (later:=cells) stored
    have nextTail : HeapList next (source+1) cells := by
      apply PDLower.CalibrationCompute.HeapList.regionMemory sourceTail nextMemory
      intro offset inside
      rw [Finset.mem_singleton]
      simp only [List.length_cons] at separate
      omega
    have tailSeparate : source+1+cells.length≤target+1 ∨ target+1+cells.length≤source+1 := by
      simp only [List.length_cons] at separate
      omega
    obtain ⟨later,after,lh,ll,lc,lt,pc,nextFresh,nextAddress,nextIndex,nextOld,tailCopied,_tailSource,output,_tailPeak,lm⟩:=
      ih (before:=next) (source:=source+1) (target:=target+1)
        rfl rfl rfl rfl old nextTail tailSeparate
    have firstValue : before.heap source=value:=PDLower.CalibrationCompute.HeapList.value stored 0 (by simp)
    have firstCopied : HeapList next target [value] := by
      change HeapList (heapCopyNext before source target cells.length origin) target [value]
      rw [←firstValue]
      exact heapCopyNext_singleton before source target cells.length origin
    have firstSurvives : HeapList after target [value] := by
      apply PDLower.CalibrationCompute.HeapList.regionMemory firstCopied (RegionMemory.trace_last lm ll)
      intro offset inside
      have zero : offset=0:=by simp only [List.length_cons,List.length_nil] at inside;omega
      subst offset
      rw [mem_cellRegion_iff]
      omega
    have copied : HeapList after target (value::cells):=
      PDLower.CalibrationCompute.HeapList.append firstSurvives tailCopied
    have currentInside : target∈cellRegion target (cells.length+1) :=
      (mem_cellRegion_iff _ _ _).mpr ⟨le_refl _,by omega⟩
    have singletonSubset : ({target} : Finset ℕ)⊆cellRegion target (cells.length+1) := by
      intro query member
      have same : query=target:=Finset.mem_singleton.mp member
      subst query
      exact currentInside
    have firstMemory : ∀ state∈first,RegionMemory before state (cellRegion target (cells.length+1)) :=
      fun state member=>(fm state member).enlarge singletonSubset
    have laterMemory : ∀ state∈later,RegionMemory next state (cellRegion target (cells.length+1)) :=
      fun state member=>(lm state member).enlarge (cellRegion_tail_subset target cells.length)
    have allMemory:=RegionMemory.join_trace first later before next (cellRegion target (cells.length+1)) fl firstMemory laterMemory
    have joined:=joinTrace_spec program input first later before next after 150 (150*cells.length+45)
      fh fl lh ll fc lc ft lt
    have sourceRetained : HeapList after source (value::cells) := by
      apply PDLower.CalibrationCompute.HeapList.regionMemory stored (RegionMemory.trace_last allMemory joined.2.1)
      intro offset inside
      rw [mem_cellRegion_iff]
      simp only [List.length_cons] at inside separate
      omega
    have allSpace : ∀ state∈joinTrace first later,workingCells state≤workingCells before+(cells.length+1) :=
      fun state member=>heapCopy_region_cells target (cells.length+1) (allMemory state member)
    have targetEq : target+1+cells.length=target+(value::cells).length := by simp only [List.length_cons];omega
    have sourceEq : source+1+cells.length=source+(value::cells).length := by simp only [List.length_cons];omega
    refine ⟨joinTrace first later,after,joined.1,joined.2.1,joined.2.2.1,
      joined.2.2.2.trans (by simp only [List.length_cons];omega),pc,?_,?_,nextIndex,nextOld,
      copied,sourceRetained,output,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory⟩
    · simpa only [targetEq] using nextFresh
    · simpa only [sourceEq] using nextAddress

end RootD27.Core
