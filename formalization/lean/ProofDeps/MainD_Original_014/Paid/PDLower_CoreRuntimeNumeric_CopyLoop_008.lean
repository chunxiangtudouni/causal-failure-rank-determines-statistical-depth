module

public import Paid.PDLower_CoreRuntimeNumeric_CopyStep_007
public import Paid.PDCompute_Pack_Sequence_046

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDLower.CoreRuntimeNumeric

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame RootD27.Core RootD27.Bits
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- One fixed nine-instruction physical heap copier for arbitrary live
source lists, runtime lengths and disjoint runtime destinations. No
destination cells, copied answers or successful execution are supplied.
Every prefix retains old live cells/output and writes only the actual
destination interval. Source cells survive and the saved return is real. -/
theorem copy_loop_resources (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (source target : ℕ) (cells : List Cell)
    (position : before.pc=origin) (address : before.register .address=.natural source)
    (fresh : before.register .fresh=.natural target) (index : before.register .index=.natural cells.length)
    (old : before.register .old=.natural (origin+9)) (stored : HeapList before source cells)
    (separate : source+cells.length≤target ∨ target+cells.length≤source)
    (budget limit : ℕ) (safe : SafeBits before budget) (small : 2≤budget)
    (limitBits : (Cell.natural limit).bits≤budget)
    (sourceEnd : source+cells.length≤limit) (targetEnd : target+cells.length≤limit)
    (pcBits : PaperProofs.Paid.Parameters.natBits (origin+9)≤budget)
    (fetched : FetchesCode program origin (heapCopyCode origin)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤150*cells.length+45 ∧ after.pc=(origin+9) ∧
      after.register .fresh=.natural (target+cells.length) ∧
      after.register .address=.natural (source+cells.length) ∧
      after.register .index=.natural 0 ∧ after.register .old=.natural (origin+9) ∧
      HeapList after target cells ∧ HeapList after source cells ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+cells.length ∧
      (∀ state∈trace,RegionMemory before state (cellRegion target cells.length)) ∧
      (∀ state∈trace,SafeBits state budget) ∧
      (∀ state∈trace,origin≤state.pc ∧ state.pc≤origin+9) ∧
      (∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+9) := by
  induction cells generalizing before source target with
  | nil =>
    obtain ⟨trace,head,last,chain,cost,properties,location,proper⟩ :=
      copy_zero_resources program input origin before budget position index old safe pcBits fetched
    have allMemory : ∀ state∈trace,RegionMemory before state (cellRegion target 0) :=
      fun state member => (properties (cellRegion target 0) state member).1
    have allSafe : ∀ state∈trace,SafeBits state budget :=
      fun state member => (properties (cellRegion target 0) state member).2
    have allSpace : ∀ state∈trace,workingCells state≤workingCells before+0 :=
      fun state member=>heapCopy_region_cells target 0 (allMemory state member)
    refine ⟨trace,{before with pc:=(origin+9)},head,last,chain,cost,rfl,fresh,address,index,old,?_,stored,rfl,
      PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,allSafe,location,proper⟩
    simp [HeapList,heapSegment]
  | cons value cells ih =>
    have live : source∈before.live:=stored.1 0 (by simp)
    obtain ⟨first,fh,fl,fc,ft,firstProperties,firstPC⟩ :=
      copy_step_resources program input origin before source target cells.length limit budget position address fresh index live
        safe small limitBits (by simp only [List.length_cons] at sourceEnd;omega)
        (by simp only [List.length_cons] at targetEnd;omega) pcBits fetched
    have fm : ∀ state∈first,RegionMemory before state {target} :=
      fun state member => (firstProperties state member).1
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
    obtain ⟨later,after,lh,ll,lc,lt,pc,nextFresh,nextAddress,nextIndex,nextOld,tailCopied,_tailSource,output,_tailPeak,lm,laterSafe,_laterPC,laterProper⟩:=
      ih (before:=next) (source:=source+1) (target:=target+1)
        rfl rfl rfl rfl old nextTail tailSeparate
        (firstProperties next (List.mem_of_getLast? fl)).2
        (by simp only [List.length_cons] at sourceEnd;omega)
        (by simp only [List.length_cons] at targetEnd;omega)
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
    have allSafe := PDCompute.Pack.joinTrace_invariant first later (fun state => SafeBits state budget)
      (fun state member => (firstProperties state member).2) laterSafe
    have laterNonempty : later≠[] := by intro empty;simp [empty] at lh
    have proper : ∀ state∈(joinTrace first later).dropLast,origin≤state.pc ∧ state.pc<origin+9 := by
      intro state member
      change state∈(first.dropLast++later).dropLast at member
      rw [List.dropLast_append_of_ne_nil laterNonempty] at member
      rcases List.mem_append.mp member with firstMember|laterMember
      · exact firstPC state (List.mem_of_mem_dropLast firstMember)
      · exact laterProper state laterMember
    have location : ∀ state∈joinTrace first later,origin≤state.pc ∧ state.pc≤origin+9 := by
      intro state member
      have split := List.dropLast_append_getLast? after (by rw [joined.2.1];simp)
      rw [←split] at member
      rcases List.mem_append.mp member with earlier|terminal
      · have bounds := proper state earlier
        omega
      · have same := List.mem_singleton.mp terminal
        subst state
        rw [pc]
        omega
    refine ⟨joinTrace first later,after,joined.1,joined.2.1,joined.2.2.1,
      joined.2.2.2.trans (by simp only [List.length_cons];omega),pc,?_,?_,nextIndex,nextOld,
      copied,sourceRetained,output,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,allSafe,location,proper⟩
    · simpa only [targetEq] using nextFresh
    · simpa only [sourceEq] using nextAddress

end PDLower.CoreRuntimeNumeric
