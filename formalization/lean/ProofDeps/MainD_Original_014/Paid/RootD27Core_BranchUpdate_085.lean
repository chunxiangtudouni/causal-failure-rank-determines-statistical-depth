module

public import Paid.RootD27Core_SelectorZero_084
public import Paid.PDLower_CoreRuntimeNumeric_CopySaved_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

/-- All three literal81-op update branches use the real saved solver
table, copy it, update the source metadata and genuinely jump to the
outer decrement. Every conclusion uses this ONE SAME-B actual trace. -/
theorem branch_update_actual (P : Parameters) (fee penalty : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (writeUpper isExact : Bool) (decrementPC budget callConstant : ℕ)
    (legalBranch : ¬(writeUpper=true ∧ isExact=true))
    (ready : PDCompute.CoreSearchLoop.Ready P fee before)
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (middlePrice : before.heap 24=.rational penalty)
    (statistics : HeapList before 25 (originalStatistics P fee penalty))
    (saved : HeapList before 46 [.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools),
      .natural (originalSolveEncoding P fee penalty).length])
    (table : HeapList before (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
      (originalSolveEncoding P fee penalty))
    (safe : RootD27.Bits.SafeBits before budget) (small : 7≤budget)
    (naturalRoom : 32*coreOperandBound P fee≤budget)
    (endBits : (Cell.natural (before.pc+81)).bits≤budget) (decrementBits : natBits decrementPC≤budget)
    (belowEntry : before.pc+81<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (fetched : FetchesCode program before.pc (branchUpdateCode before.pc writeUpper isExact decrementPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤150*(originalSolveEncoding P fee penalty).length+1200 ∧
      after.pc=decrementPC ∧ PDCompute.CoreSearchLoop.Ready P fee after ∧
      SearchStateRep P fee after (updatedSourceState P fee penalty lower upper writeUpper isExact) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (savedCopyRegion P fee penalty writeUpper∪scalarRegion)) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      peakCells trace≤workingCells before+(originalSolveEncoding P fee penalty).length+3 ∧
      (∀ state∈trace,(before.pc≤state.pc ∧ state.pc≤before.pc+80) ∨ state.pc=decrementPC) ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+81) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 ∧
      SolverCallRefinement program labels P fee callConstant trace := by
  change FetchesCode program before.pc (copySavedResultCode before.pc writeUpper++
    headerCode (selectedMetadataCommands writeUpper isExact)++[.jump decrementPC]) at fetched
  simp only [List.append_assoc] at fetched
  have copyEndBits : (Cell.natural (before.pc+52)).bits≤budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : before.pc+52≤before.pc+81)) 1).trans endBits
  obtain ⟨copy,copied,copyHead,copyLast,copyChain,copyCost,copiedPC,copiedFresh,copiedTable,copiedLength,
    _copiedPrepared,copyOutput,copySpace,copyMemory,copyScope,copySafe,copyProper⟩:=
    PDLower.CoreRuntimeNumeric.copy_saved_resources P fee penalty program input before writeUpper ready.prepared
      saved table fetched.append_left budget safe naturalRoom copyEndBits
  have copiedMemory : RegionMemory before copied (savedCopyRegion P fee penalty writeUpper):=
    copyMemory copied (List.mem_of_getLast? copyLast)
  have metadataFetch : FetchesCode program copied.pc (headerCode (selectedMetadataCommands writeUpper isExact)) := by
    rw [copiedPC]
    simpa only [copySavedResult_length] using fetched.append_right.append_left
  have metadataPCBits : natBits (copied.pc+28)≤budget := by
    have bound := PDROC.DataBits.natBits_mono (by rw [copiedPC];omega : copied.pc+28≤before.pc+81)
    change 1+natBits (before.pc+81)≤budget at endBits
    omega
  obtain ⟨metadata,updated,metadataHead,metadataLast,metadataChain,metadataCost,updatedPC,updatedFresh,updatedHeader,
    updatedRep,updatedPrepared,updatedCache,counter,output,metadataMemory,metadataProperties,metadataScope,
    _metadataProper,metadataSpace,_metadataRequests,_metadataCount⟩:=
    updated_metadata_actual P fee penalty lower upper program labels input before copied writeUpper isExact budget
      legalBranch ready.header ready.prepared ready.cache represented copiedMemory copiedFresh middlePrice statistics
      copiedTable copiedLength (copySafe copied (List.mem_of_getLast? copyLast)) small metadataPCBits
      (by rw [copiedPC];omega) metadataFetch
  have jumpFetch : program[updated.pc]?=some (.jump decrementPC) := by
    rw [updatedPC,copiedPC]
    simpa only [copySavedResult_length,selectedMetadata_length,Nat.add_zero,List.getElem?_cons_zero] using
      fetched.append_right.append_right 0 (by change 0<1;decide)
  let after : State:={updated with pc:=decrementPC}
  have jump : step program input updated=some after:=by simp only [step,jumpFetch];rfl
  have controlled:=chain_append_control program input metadata updated after metadataChain metadataLast jump
  have metadataNonempty : metadata≠[]:=by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at metadataHead
  have updatedSafe : RootD27.Bits.SafeBits updated budget:=
    (metadataProperties updated (List.mem_of_getLast? metadataLast)).2
  have afterSafe : RootD27.Bits.SafeBits after budget:=updatedSafe.withPC decrementPC decrementBits
  have tailHead : (metadata++[after]).head?=some copied := by
    simpa only [List.head?_append_of_ne_nil metadata metadataNonempty] using metadataHead
  have tailLast : (metadata++[after]).getLast?=some after:=by simp
  have joined:=joinTrace_spec program input copy (metadata++[after]) before copied after
    (150*(originalSolveEncoding P fee penalty).length+750) 450
    copyHead copyLast tailHead tailLast copyChain controlled.1 copyCost (by omega)
  let region:=savedCopyRegion P fee penalty writeUpper∪scalarRegion
  have allMemory : ∀ state∈joinTrace copy (metadata++[after]),RegionMemory before state region := by
    intro state member
    rcases joinTrace_member member with copyMember|tailMember
    · exact (copyMemory state copyMember).enlarge Finset.subset_union_left
    · rcases List.mem_append.mp tailMember with metadataMember|terminal
      · exact (copiedMemory.enlarge Finset.subset_union_left).trans
          (((metadataProperties state metadataMember).1).enlarge Finset.subset_union_right)
      · have same:=List.mem_singleton.mp terminal
        subst state
        exact (copiedMemory.enlarge Finset.subset_union_left).trans
          ((metadataProperties updated (List.mem_of_getLast? metadataLast)).1.enlarge Finset.subset_union_right)
  have tailSafe : ∀ state∈metadata++[after],RootD27.Bits.SafeBits state budget := by
    intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact (metadataProperties state earlier).2
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact afterSafe
  have allSafe:=PDCompute.Pack.joinTrace_invariant copy (metadata++[after])
    (fun state=>RootD27.Bits.SafeBits state budget) copySafe tailSafe
  have copiedBound:=(workingCells_le_peak_of_member copy copied (List.mem_of_getLast? copyLast)).trans copySpace
  have updatedBound:=(workingCells_le_peak_of_member metadata updated (List.mem_of_getLast? metadataLast)).trans metadataSpace
  have allSpace : ∀ state∈joinTrace copy (metadata++[after]),
      workingCells state≤workingCells before+(originalSolveEncoding P fee penalty).length+3 := by
    intro state member
    rcases joinTrace_member member with copyMember|tailMember
    · exact (workingCells_le_peak_of_member copy state copyMember).trans copySpace
    · rcases List.mem_append.mp tailMember with metadataMember|terminal
      · exact ((workingCells_le_peak_of_member metadata state metadataMember).trans metadataSpace).trans copiedBound
      · have same:=List.mem_singleton.mp terminal
        subst state
        exact updatedBound.trans copiedBound
  have allScope : ∀ state∈joinTrace copy (metadata++[after]),
      (before.pc≤state.pc ∧ state.pc≤before.pc+80) ∨ state.pc=decrementPC := by
    intro state member
    rcases joinTrace_member member with copyMember|tailMember
    · have bounds:=copyScope state copyMember
      exact Or.inl ⟨bounds.1,by omega⟩
    · rcases List.mem_append.mp tailMember with metadataMember|terminal
      · have bounds:=metadataScope state metadataMember
        rw [copiedPC] at bounds
        exact Or.inl ⟨by omega,by omega⟩
      · have same:=List.mem_singleton.mp terminal
        subst state
        exact Or.inr rfl
  have proper : ∀ state∈(joinTrace copy (metadata++[after])).dropLast,
      before.pc≤state.pc ∧ state.pc<before.pc+81 := by
    intro state member
    change state∈(copy.dropLast++(metadata++[after])).dropLast at member
    have tailNonempty : metadata++[after]≠[]:=by simp
    rw [List.dropLast_append_of_ne_nil tailNonempty] at member
    rcases List.mem_append.mp member with copyMember|metadataMember
    · have bounds:=copyProper state copyMember
      omega
    · have actualMember : state∈metadata:=by simpa using metadataMember
      have bounds:=metadataScope state actualMember
      rw [copiedPC] at bounds
      omega
  have excluded : ∀ state∈joinTrace copy (metadata++[after]),state.pc≠labels.solveEntry := by
    intro state member
    rcases allScope state member with inline|terminal <;> omega
  have noCalls:=no_solve_entry labels (joinTrace copy (metadata++[after])) excluded
  have refinement:=PDCompute.CoreSearchLoop.refinement_of_no_entry program labels P fee callConstant
    (joinTrace copy (metadata++[after])) excluded
  have afterRep : SearchStateRep P fee after (updatedSourceState P fee penalty lower upper writeUpper isExact) := by
    cases writeUpper <;> cases isExact <;> exact updatedRep
  exact ⟨joinTrace copy (metadata++[after]),after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans (by omega),rfl,
    ⟨updatedHeader,updatedFresh,updatedPrepared,updatedCache⟩,afterRep,counter,output,allMemory,allSafe,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allScope,proper,noCalls.1,noCalls.2,refinement⟩

end RootD27.Core
