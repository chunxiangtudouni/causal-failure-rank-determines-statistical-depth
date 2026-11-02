module

public import Paid.RootD27Core_SearchRepresentation_056

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

def retainedCommitBlockCode (origin : ℕ) (upper : Bool) : List Instruction :=
  retainedCopyCode origin upper (origin+29)++retainedCommitCode (tableLengthSlot upper)

theorem retainedCommitBlock_length (origin : ℕ) (upper : Bool) :
    (retainedCommitBlockCode origin upper).length=34 := by
  simp only [retainedCommitBlockCode,List.length_append,retainedCopy_length,retainedCommit_length]

/-- The returned table is really copied, its saved length is really
loaded and committed, then fresh0 is really restored. One fixed34-op
inline block; no external encoded length or zero-header assumption. -/
theorem retained_commit_block_actual (P : Parameters) (fee penalty : ℚ)
    (program : Program) (input : List Cell) (before : State) (base : ℕ) (upper : Bool)
    (prepared : HeapList before 0 (preparedInput P fee))
    (fresh : before.register .fresh=.natural base)
    (address : before.register .address=.natural (resultBase base P.certificate.stages P.tools))
    (index : before.register .index=.natural (originalSolveEncoding P fee penalty).length)
    (table : HeapList before (resultBase base P.certificate.stages P.tools) (originalSolveEncoding P fee penalty))
    (fetched : FetchesCode program before.pc (retainedCommitBlockCode before.pc upper)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤150*(originalSolveEncoding P fee penalty).length+465 ∧
      after.pc=before.pc+34 ∧ after.register .fresh=.natural 0 ∧
      after.register .index=.natural (originalSolveEncoding P fee penalty).length ∧
      HeapList after (retainedTableBase base P.certificate.stages P.tools upper) (originalSolveEncoding P fee penalty) ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after (tableLengthSlot upper) [.natural (originalSolveEncoding P fee penalty).length] ∧
      after.output=before.output ∧ peakCells trace≤workingCells before+(originalSolveEncoding P fee penalty).length+3 ∧
      (∀ state∈trace,RegionMemory before state
        (retainedCopyRegion base P.certificate.stages P.tools (originalSolveEncoding P fee penalty).length upper∪{tableLengthSlot upper})) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+34) := by
  let cells:=originalSolveEncoding P fee penalty
  let region:=retainedCopyRegion base P.certificate.stages P.tools cells.length upper∪{tableLengthSlot upper}
  change FetchesCode program before.pc
    (retainedCopyCode before.pc upper (before.pc+29)++retainedCommitCode (tableLengthSlot upper)) at fetched
  obtain ⟨copy,copied,ch,cl,cc,ct,copyPC,_copyOld,_copyIndex,copiedTable,_source,preparedCopied,copyOutput,copyPeak,copyMemory,copyScope,saved⟩:=
    retained_table_copy_saved_in_caller P fee penalty program input before base (before.pc+29) upper
      prepared fresh address index table fetched.append_left
  change peakCells copy≤workingCells before+cells.length+2 at copyPeak
  have savedCount : HeapList copied 47 [.natural cells.length] :=
    PDLower.CalibrationCompute.HeapList.append_right
      (first:=[.natural (resultBase base P.certificate.stages P.tools)]) (later:=[.natural cells.length]) saved
  have commitFetch : FetchesCode program copied.pc (retainedCommitCode (tableLengthSlot upper)) := by
    rw [copyPC]
    simpa only [retainedCopy_length] using fetched.append_right
  obtain ⟨commit,mh,ml,mc,mt,commitMemory,commitScope,commitPeak,lengthStored⟩:=
    retainedCommit_actual program input copied (tableLengthSlot upper) cells.length savedCount commitFetch
  let after:=retainedCommitResult copied (tableLengthSlot upper) cells.length
  have lastMemory:=commitMemory after (List.mem_of_getLast? ml)
  have slotLower : 13≤tableLengthSlot upper:=(tableLengthSlot_bounds upper).1
  have slotUpper : tableLengthSlot upper<46:=(tableLengthSlot_bounds upper).2
  have targetLower : 48≤retainedTableBase base P.certificate.stages P.tools upper := by
    have bound:=retained_base_above_workspace base P.certificate.stages P.tools upper
    unfold workspaceSize headerWords at bound
    omega
  have finalTable : HeapList after (retainedTableBase base P.certificate.stages P.tools upper) cells := by
    apply lastMemory.heapList copiedTable
    intro offset _inside
    simp only [Finset.mem_singleton]
    omega
  have finalPrepared : HeapList after 0 (preparedInput P fee) := by
    apply lastMemory.heapList preparedCopied
    intro offset inside
    change offset<13 at inside
    simp only [Finset.mem_singleton]
    omega
  have copiedMemory:=RegionMemory.trace_last copyMemory cl
  have allMemory:=RegionMemory.join_trace copy commit before copied region cl
    (fun state member=>(copyMemory state member).enlarge Finset.subset_union_left)
    (fun state member=>(commitMemory state member).enlarge Finset.subset_union_right)
  have joined:=joinTrace_spec program input copy commit before copied after (150*cells.length+375) 90
    ch cl mh ml cc mc ct mt
  have copiedBound:=(workingCells_le_peak_of_member copy copied (List.mem_of_getLast? cl)).trans copyPeak
  have allSpace : ∀ state∈joinTrace copy commit,workingCells state≤workingCells before+cells.length+3 := by
    intro state member
    rcases joinTrace_member member with copiedMember|commitMember
    · have bound:=(workingCells_le_peak_of_member copy state copiedMember).trans copyPeak
      omega
    · have bound:=(workingCells_le_peak_of_member commit state commitMember).trans commitPeak
      omega
  have pcs : ∀ state∈joinTrace copy commit,before.pc≤state.pc ∧ state.pc≤before.pc+34 := by
    intro state member
    rcases joinTrace_member member with copiedMember|commitMember
    · have split:=List.dropLast_append_getLast? copied (by rw [cl];simp)
      rw [←split] at copiedMember
      rcases List.mem_append.mp copiedMember with proper|terminal
      · have bound:=copyScope state proper
        omega
      · have same : state=copied:=List.mem_singleton.mp terminal
        subst state
        rw [copyPC]
        omega
    · have bound:=commitScope state commitMember
      rw [copyPC] at bound
      omega
  have finalPC : after.pc=before.pc+34 := by
    change copied.pc+5=before.pc+34
    rw [copyPC]
  have finalTime : time program (joinTrace copy commit)≤150*(originalSolveEncoding P fee penalty).length+465 := by
    change time program (joinTrace copy commit)≤150*cells.length+465
    exact joined.2.2.2.trans (by omega)
  exact ⟨joinTrace copy commit,after,joined.1,joined.2.1,joined.2.2.1,finalTime,finalPC,rfl,rfl,
    finalTable,finalPrepared,lengthStored,lastMemory.2.2.2.trans copyOutput,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,pcs⟩

end RootD27.Core
