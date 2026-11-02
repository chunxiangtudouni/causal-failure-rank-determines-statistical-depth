module

public import Paid.RootD27Core_RestoreResult_067

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

def copySavedResultCode (origin : ℕ) (upper : Bool) : List Instruction :=
  restoreSolverResultCode (origin+18)++retainedCommitBlockCode (origin+18) upper

theorem copySavedResult_length (origin : ℕ) (upper : Bool) :
    (copySavedResultCode origin upper).length=52 := by
  simp only [copySavedResultCode,List.length_append,restoreSolverResult_length,retainedCommitBlock_length]

/-- After actual scalar comparisons, restore the real saved result and
physically copy it to the selected source-state buffer. The source table
is the real solver output and no register values are input premises. -/
theorem copy_saved_result_actual (P : Parameters) (fee penalty : ℚ) (program : Program) (input : List Cell)
    (before : State) (upper : Bool) (prepared : HeapList before 0 (preparedInput P fee))
    (saved : HeapList before 46
      [.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools),
       .natural (originalSolveEncoding P fee penalty).length])
    (table : HeapList before (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
      (originalSolveEncoding P fee penalty))
    (fetched : FetchesCode program before.pc (copySavedResultCode before.pc upper)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤150*(originalSolveEncoding P fee penalty).length+750 ∧
      after.pc=before.pc+52 ∧ after.register .fresh=.natural 0 ∧
      HeapList after (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper)
        (originalSolveEncoding P fee penalty) ∧
      HeapList after (tableLengthSlot upper) [.natural (originalSolveEncoding P fee penalty).length] ∧
      HeapList after 0 (preparedInput P fee) ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+(originalSolveEncoding P fee penalty).length+3 ∧
      (∀ state∈trace,RegionMemory before state
        (retainedCopyRegion (99+2*P.certificate.M) P.certificate.stages P.tools
          (originalSolveEncoding P fee penalty).length upper∪{tableLengthSlot upper})) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+52) := by
  let base:=99+2*P.certificate.M
  let cells:=originalSolveEncoding P fee penalty
  let source:=resultBase base P.certificate.stages P.tools
  let region:=retainedCopyRegion base P.certificate.stages P.tools cells.length upper∪{tableLengthSlot upper}
  let restored:=restoreSolverResult P fee before (before.pc+18) source cells.length
  change FetchesCode program before.pc
    (restoreSolverResultCode (before.pc+18)++retainedCommitBlockCode (before.pc+18) upper) at fetched
  obtain ⟨restore,rh,rl,rc,rt,restoredFresh,restoredAddress,restoredIndex,restoreMemory,restoreScope,restorePeak⟩:=
    restore_solver_result_actual P fee program input before (before.pc+18) source cells.length
      prepared saved fetched.append_left
  have restoredPC : restored.pc=before.pc+18:=rfl
  have copyFetch : FetchesCode program restored.pc (retainedCommitBlockCode restored.pc upper) := by
    rw [restoredPC]
    simpa only [restoreSolverResult_length] using fetched.append_right
  obtain ⟨copy,after,ch,cl,cc,ct,afterPC,afterFresh,_index,retained,preparedAfter,lengthAfter,
    output,copyPeak,copyMemory,copyScope⟩:=
    retained_commit_block_actual P fee penalty program input restored base upper prepared
      restoredFresh restoredAddress restoredIndex table copyFetch
  change peakCells copy≤workingCells before+cells.length+3 at copyPeak
  change time program copy≤150*cells.length+465 at ct
  have joined:=joinTrace_spec program input restore copy before restored after 285 (150*cells.length+465)
    rh rl ch cl rc cc rt ct
  have middleMemory : RegionMemory before restored region:=RegionMemory.refl before region
  have allMemory : ∀ state∈joinTrace restore copy,RegionMemory before state region := by
    intro state member
    rcases joinTrace_member member with restoreMember|copyMember
    · have fields:=restoreMemory state restoreMember
      refine ⟨fun address _outside=>congrFun fields.1 address,?_,?_,fields.2.2⟩
      · rw [fields.2.1]
        exact Finset.subset_union_left
      · rw [fields.2.1]
    · exact middleMemory.trans (copyMemory state copyMember)
  have allSpace : ∀ state∈joinTrace restore copy,workingCells state≤workingCells before+cells.length+3 := by
    intro state member
    rcases joinTrace_member member with restoreMember|copyMember
    · have bound:=workingCells_le_peak_of_member restore state restoreMember
      exact bound.trans (restorePeak.trans (by omega))
    · exact (workingCells_le_peak_of_member copy state copyMember).trans copyPeak
  have allPC : ∀ state∈joinTrace restore copy,before.pc≤state.pc ∧ state.pc≤before.pc+52 := by
    intro state member
    rcases joinTrace_member member with restoreMember|copyMember
    · have scope:=restoreScope state restoreMember
      omega
    · have scope:=copyScope state copyMember
      omega
  exact ⟨joinTrace restore copy,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans (by
      change 285+(150*cells.length+465)≤150*cells.length+750
      omega),
    by omega,afterFresh,retained,lengthAfter,preparedAfter,output,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,allPC⟩

end RootD27.Core
