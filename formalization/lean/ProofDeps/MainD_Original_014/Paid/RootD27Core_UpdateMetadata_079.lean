module

public import Paid.RootD27Core_StopDecision_078

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

def updatedSourceState (P : Parameters) (fee penalty : ℚ) (lower upper : MultiplierSolve) :
    Bool→Bool→MultiplierState
  | false,true=>.exact (P.cachedSolveMultiplier P.endpointCache fee penalty)
  | false,false=>.bracket (P.cachedSolveMultiplier P.endpointCache fee penalty) upper
  | true,_=>.bracket lower (P.cachedSolveMultiplier P.endpointCache fee penalty)

theorem selectedMetadata_below_outside (written : Bool) (address : ℕ) (below : address<13) :
    address∉selectedMetadataRegion written := by
  cases written <;> simp only [selectedMetadataRegion,multiplierSlot,statisticsSlot,
    Bool.false_eq_true,ite_false,ite_true,Finset.mem_insert,Finset.mem_singleton] <;> omega

/-- Joint metadata execution and source update, consuming the real
preceding copy's footprint and table. In particular the source invariant
is not assumed after overwriting its selected old table. -/
theorem updated_metadata_actual (P : Parameters) (fee penalty : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before copied : State)
    (writeUpper isExact : Bool) (budget : ℕ)
    (legalBranch : ¬(writeUpper=true ∧ isExact=true))
    (header : Header before 0 (fun slot=>before.heap slot))
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (copyMemory : RegionMemory before copied (savedCopyRegion P fee penalty writeUpper))
    (fresh : copied.register .fresh=.natural 0)
    (middlePrice : before.heap 24=.rational penalty)
    (statistics : HeapList before 25 (originalStatistics P fee penalty))
    (table : HeapList copied
      (retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools writeUpper)
      (originalSolveEncoding P fee penalty))
    (length : HeapList copied (tableLengthSlot writeUpper) [.natural (originalSolveEncoding P fee penalty).length])
    (safe : RootD27.Bits.SafeBits copied budget) (small : 7≤budget)
    (pcBits : natBits (copied.pc+28)≤budget) (belowEntry : copied.pc+28<labels.solveEntry)
    (fetched : FetchesCode program copied.pc (headerCode (selectedMetadataCommands writeUpper isExact))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some copied ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤435 ∧
      after.pc=copied.pc+28 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧
      SearchStateRep P fee after (updatedSourceState P fee penalty lower upper writeUpper isExact) ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      RegionMemory copied after (selectedMetadataRegion writeUpper) ∧
      (∀ state∈trace,RegionMemory copied state scalarRegion ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,copied.pc≤state.pc ∧ state.pc≤copied.pc+28) ∧
      (∀ state∈trace.dropLast,state.pc<copied.pc+28) ∧ peakCells trace≤workingCells copied ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 := by
  have copiedFields:=savedCopy_header_fields P fee penalty writeUpper before copied header copyMemory
  have copiedPrice : copied.heap 24=.rational penalty:=copiedFields.2.1.trans middlePrice
  obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,pc,metadataMemory,output,
    properties,scope,proper,space⟩:=
    PDLower.CoreRuntimeNumeric.selected_metadata_resources program input copied (fun slot=>copied.heap slot)
      writeUpper isExact budget copiedFields.1 fresh safe small pcBits fetched
  have afterRep : SearchStateRep P fee after
      (updatedSourceState P fee penalty lower upper writeUpper isExact) := by
    cases writeUpper with
    | false =>
      cases isExact with
      | false =>
        exact lower_update_rep P fee penalty upper before copied after (fun slot=>copied.heap slot)
          represented.2.1 represented.2.2.2.2 copyMemory copiedFields.1 afterHeader metadataMemory
          copiedPrice statistics table length
      | true =>
        exact exact_update_rep P fee penalty before copied after (fun slot=>copied.heap slot)
          copyMemory copiedFields.1 afterHeader metadataMemory copiedPrice statistics table length
    | true =>
      cases isExact with
      | false =>
        exact upper_update_rep P fee penalty lower before copied after (fun slot=>copied.heap slot)
          represented.1 represented.2.2.2.1 copyMemory copiedFields.1 afterHeader metadataMemory
          copiedPrice statistics table length
      | true => exact False.elim (legalBranch ⟨rfl,rfl⟩)
  have copiedPrepared:=savedCopy_prepared P fee penalty writeUpper before copied prepared copyMemory
  have copiedCache:=savedCopy_cache P fee penalty writeUpper before copied stored copyMemory
  have finalPrepared : HeapList after 0 (preparedInput P fee) := by
    apply metadataMemory.heapList copiedPrepared
    intro offset inside
    change offset<13 at inside
    exact selectedMetadata_below_outside writeUpper (0+offset) (by omega)
  have finalCache : HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
    apply metadataMemory.heapList copiedCache
    intro offset _inside
    exact selectedMetadata_above_outside writeUpper (96+offset) (by omega)
  have finalCounter : after.heap 28=before.heap 28:=
    (metadataMemory.1 28 (selectedMetadata_above_outside writeUpper 28 (by decide))).trans copiedFields.2.2.2
  have liveHeader : Header after 0 (fun slot=>after.heap slot) := by
    intro slot inside
    exact ⟨afterHeader.live slot inside,by simp only [Nat.zero_add]⟩
  have noCalls:=no_solve_entry labels trace (by
    intro state member
    have bound:=(scope state member).2
    omega)
  exact ⟨trace,after,head,last,chain,cost,pc,afterFresh,liveHeader,afterRep,finalPrepared,finalCache,
    finalCounter,output.trans copyMemory.2.2.2,metadataMemory,
    (fun state member=>⟨scalar_region_memory (properties state member).1,(properties state member).2⟩),
    scope,proper,space,noCalls.1,noCalls.2⟩

end RootD27.Core
