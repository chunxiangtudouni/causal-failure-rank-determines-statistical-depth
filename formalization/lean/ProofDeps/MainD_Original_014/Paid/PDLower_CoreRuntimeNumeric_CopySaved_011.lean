module

public import Paid.PDLower_CoreRuntimeNumeric_RetainedCopyCommit_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

@[expose] public section

namespace PDLower.CoreRuntimeNumeric

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame RootD27.Core RootD27.Bits
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- The returned table is really copied, its saved length is really
loaded and committed, then fresh0 is really restored. One fixed34-op
inline block; no external encoded length or zero-header assumption. -/
theorem commit_block_resources (P : Parameters) (fee penalty : ℚ)
    (program : Program) (input : List Cell) (before : State) (base : ℕ) (upper : Bool)
    (prepared : HeapList before 0 (preparedInput P fee))
    (fresh : before.register .fresh=.natural base)
    (address : before.register .address=.natural (resultBase base P.certificate.stages P.tools))
    (index : before.register .index=.natural (originalSolveEncoding P fee penalty).length)
    (table : HeapList before (resultBase base P.certificate.stages P.tools) (originalSolveEncoding P fee penalty))
    (fetched : FetchesCode program before.pc (retainedCommitBlockCode before.pc upper))
    (budget : ℕ) (safe : SafeBits before budget) (small : 7≤budget) (baseLower : 99≤base)
    (limitBits : (Cell.natural (base+78*PDCompute.Solver.entryCount P.certificate.stages P.tools)).bits≤budget)
    (endBits : (Cell.natural (before.pc+34)).bits≤budget) :
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
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+34) ∧
      (∀ state∈trace,SafeBits state budget) ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+34) := by
  let cells:=originalSolveEncoding P fee penalty
  let region:=retainedCopyRegion base P.certificate.stages P.tools cells.length upper∪{tableLengthSlot upper}
  change FetchesCode program before.pc
    (retainedCopyCode before.pc upper (before.pc+29)++retainedCommitCode (tableLengthSlot upper)) at fetched
  obtain ⟨copy,copied,ch,cl,cc,ct,copyPC,_copyOld,_copyIndex,copiedTable,_source,preparedCopied,copyOutput,copyPeak,copyMemory,saved,copySafe,copyClosed,copyScope⟩:=
    retained_copy_resources P fee penalty program input before base budget upper
      prepared fresh address index table fetched.append_left safe baseLower limitBits
      ((Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : before.pc+29≤before.pc+34)) 1).trans endBits)
  change peakCells copy≤workingCells before+cells.length+2 at copyPeak
  have savedCount : HeapList copied 47 [.natural cells.length] :=
    PDLower.CalibrationCompute.HeapList.append_right
      (first:=[.natural (resultBase base P.certificate.stages P.tools)]) (later:=[.natural cells.length]) saved
  have commitFetch : FetchesCode program copied.pc (retainedCommitCode (tableLengthSlot upper)) := by
    rw [copyPC]
    simpa only [retainedCopy_length] using fetched.append_right
  have slotBits : (Cell.natural (tableLengthSlot upper)).bits≤budget :=
    ((Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by have b:=(tableLengthSlot_bounds upper).2;omega : tableLengthSlot upper≤47)) 1).trans
      (show 1+PaperProofs.Paid.Parameters.natBits 47≤7 by decide)).trans small
  have endPCBits : PaperProofs.Paid.Parameters.natBits (before.pc+34)≤budget := by
    change 1+PaperProofs.Paid.Parameters.natBits (before.pc+34)≤budget at endBits
    omega
  obtain ⟨commit,mh,ml,mc,mt,commitProperties,commitScope,commitProper,commitPeak,lengthStored⟩:=
    commit_resources program input copied (tableLengthSlot upper) cells.length budget savedCount
      (copySafe copied (List.mem_of_getLast? cl)) small slotBits (by rw [copyPC];exact endPCBits) commitFetch
  have commitMemory : ∀ state∈commit,RegionMemory copied state {tableLengthSlot upper} :=
    fun state member => (commitProperties state member).1
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
  change time program copy≤150*cells.length+360 at ct
  have joined:=joinTrace_spec program input copy commit before copied after (150*cells.length+375) 90
    ch cl mh ml cc mc (ct.trans (by omega)) mt
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
  have allSafe := PDCompute.Pack.joinTrace_invariant copy commit (fun state => SafeBits state budget)
    copySafe (fun state member => (commitProperties state member).2)
  have commitNonempty : commit≠[] := by intro empty;simp [empty] at mh
  have proper : ∀ state∈(joinTrace copy commit).dropLast,before.pc≤state.pc ∧ state.pc<before.pc+34 := by
    intro state member
    change state∈(copy.dropLast++commit).dropLast at member
    rw [List.dropLast_append_of_ne_nil commitNonempty] at member
    rcases List.mem_append.mp member with copyMember|commitMember
    · have bounds := copyScope state copyMember
      omega
    · have low := (commitScope state (List.mem_of_mem_dropLast commitMember)).1
      have high := commitProper state commitMember
      rw [copyPC] at low high
      omega
  exact ⟨joinTrace copy commit,after,joined.1,joined.2.1,joined.2.2.1,finalTime,finalPC,rfl,rfl,
    finalTable,finalPrepared,lengthStored,lastMemory.2.2.2.trans copyOutput,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,pcs,allSafe,proper⟩

/-- After actual scalar comparisons, restore the real saved result and
physically copy it to the selected source-state buffer. The source table
is the real solver output and no register values are input premises. -/
theorem copy_saved_resources (P : Parameters) (fee penalty : ℚ) (program : Program) (input : List Cell)
    (before : State) (upper : Bool) (prepared : HeapList before 0 (preparedInput P fee))
    (saved : HeapList before 46
      [.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools),
       .natural (originalSolveEncoding P fee penalty).length])
    (table : HeapList before (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
      (originalSolveEncoding P fee penalty))
    (fetched : FetchesCode program before.pc (copySavedResultCode before.pc upper))
    (budget : ℕ) (safe : SafeBits before budget) (naturalRoom : 32*coreOperandBound P fee≤budget)
    (endBits : (Cell.natural (before.pc+52)).bits≤budget) :
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
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+52) ∧
      (∀ state∈trace,SafeBits state budget) ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+52) := by
  let base:=99+2*P.certificate.M
  let cells:=originalSolveEncoding P fee penalty
  let source:=resultBase base P.certificate.stages P.tools
  let region:=retainedCopyRegion base P.certificate.stages P.tools cells.length upper∪{tableLengthSlot upper}
  let restored:=restoreSolverResult P fee before (before.pc+18) source cells.length
  change FetchesCode program before.pc
    (restoreSolverResultCode (before.pc+18)++retainedCommitBlockCode (before.pc+18) upper) at fetched
  have positive : 1≤coreOperandBound P fee := by unfold coreOperandBound;omega
  have small : 7≤budget := by omega
  have baseBits : (Cell.natural base).bits≤budget :=
    runtime_natural_room P fee budget base naturalRoom (runtime_base_le_limit P)
  have limitBits : (Cell.natural (runtimeAddressLimit P)).bits≤budget :=
    (runtime_address_room_le_core P fee).trans naturalRoom
  have returnBits : (Cell.natural (before.pc+18)).bits≤budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : before.pc+18≤before.pc+52)) 1).trans endBits
  have restorePCBits : PaperProofs.Paid.Parameters.natBits (before.pc+18)≤budget := by
    change 1+PaperProofs.Paid.Parameters.natBits (before.pc+18)≤budget at returnBits
    omega
  obtain ⟨restore,rh,rl,rc,rt,restoreProperties,restoreScope,restoreProper,restorePeak⟩:=
    restore_resources P fee program input before (before.pc+18) source cells.length budget safe prepared saved
      small baseBits returnBits restorePCBits fetched.append_left
  have restoreMemory : ∀ state∈restore,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output :=
    fun state member => (restoreProperties state member).1
  have restoredFresh : restored.register .fresh=.natural base := by simp [restored,restoreSolverResult,solverRuntimeArgumentsResult,base]
  have restoredAddress : restored.register .address=.natural source := by simp [restored,restoreSolverResult]
  have restoredIndex : restored.register .index=.natural cells.length := by simp [restored,restoreSolverResult]
  have restoredPC : restored.pc=before.pc+18:=rfl
  have copyFetch : FetchesCode program restored.pc (retainedCommitBlockCode restored.pc upper) := by
    rw [restoredPC]
    simpa only [restoreSolverResult_length] using fetched.append_right
  obtain ⟨copy,after,ch,cl,cc,ct,afterPC,afterFresh,_index,retained,preparedAfter,lengthAfter,
    output,copyPeak,copyMemory,copyScope,copySafe,copyProper⟩:=
    commit_block_resources P fee penalty program input restored base upper prepared
      restoredFresh restoredAddress restoredIndex table copyFetch budget
      (restoreProperties restored (List.mem_of_getLast? rl)).2 small (by dsimp only [base];omega) limitBits
      (by simpa only [restored,restoreSolverResult,solverRuntimeArgumentsResult,Nat.add_assoc] using endBits)
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
  have allSafe := PDCompute.Pack.joinTrace_invariant restore copy (fun state => SafeBits state budget)
    (fun state member => (restoreProperties state member).2) copySafe
  have copyNonempty : copy≠[] := by intro empty;simp [empty] at ch
  have proper : ∀ state∈(joinTrace restore copy).dropLast,before.pc≤state.pc ∧ state.pc<before.pc+52 := by
    intro state member
    change state∈(restore.dropLast++copy).dropLast at member
    rw [List.dropLast_append_of_ne_nil copyNonempty] at member
    rcases List.mem_append.mp member with restoreMember|copyMember
    · have low := (restoreScope state (List.mem_of_mem_dropLast restoreMember)).1
      have high := restoreProper state restoreMember
      omega
    · have bounds := copyProper state copyMember
      rw [restoredPC] at bounds
      omega
  exact ⟨joinTrace restore copy,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans (by
      change 285+(150*cells.length+465)≤150*cells.length+750
      omega),
    by omega,afterFresh,retained,lengthAfter,preparedAfter,output,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,allPC,allSafe,proper⟩


end PDLower.CoreRuntimeNumeric
