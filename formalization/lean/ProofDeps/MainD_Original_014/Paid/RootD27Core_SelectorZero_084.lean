module

public import Paid.RootD27Core_FinalBoundary_083

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

theorem prepared_selector_fields (P : Parameters) (fee : ℚ) (state : State)
    (prepared : HeapList state 0 (preparedInput P fee)) :
    state.heap 12=.rational (P.zeroChargeRisk fee) ∧ state.heap 3=.rational P.certificate.risk := by
  have zeroValue:=PDLower.CalibrationCompute.HeapList.value prepared 12 (by change 12<13;decide)
  have riskValue:=PDLower.CalibrationCompute.HeapList.value prepared 3 (by change 3<13;decide)
  exact ⟨zeroValue,riskValue⟩

/-- The real four-instruction zero selector, used only after the actual
zero-risk or exact-source branch. It preserves all physical source data,
with exact PC, same-B resources and no solver entry on this SAME trace. -/
theorem represented_selector_zero_actual (P : Parameters) (fee : ℚ) (source : MultiplierState)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (budget callConstant : ℕ) (ready : PDCompute.CoreSearchLoop.Ready P fee before)
    (represented : SearchStateRep P fee before source)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+4)≤budget)
    (belowEntry : before.pc+4<labels.solveEntry)
    (fetched : FetchesCode program before.pc (headerCode selectorZeroCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤75 ∧
      after.pc=before.pc+4 ∧ PDCompute.CoreSearchLoop.Ready P fee after ∧
      SearchStateRep P fee after source ∧ after.heap 29=.rational 0 ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧ RegionMemory before after {29} ∧
      (∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+4) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+4) ∧ peakCells trace≤workingCells before ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 ∧
      SolverCallRefinement program labels P fee callConstant trace := by
  have zeroBits : (.rational (0:ℚ) : Cell).bits≤budget := by
    norm_num [Cell.bits,ratEncodingBits,ratNumBits,ratDenBits,natBits]
    omega
  obtain ⟨after,actual,afterHeader,afterFresh,pc⟩:=PDLower.CoreSearch.Located.literal_segment_bits
    program input before (fun slot=>before.heap slot) 29 budget (.rational 0) (by decide) ready.header ready.fresh
    safe zeroBits addressBits pcBits fetched before.pc (before.pc+4) (le_refl _) (le_refl _)
  have finalFields:=actual.final.1
  have precise : RegionMemory before after {29} := by
    apply header_final_values_region _ ready.header afterHeader finalFields
    intro slot _inside outside
    have different : slot≠29:=by simpa only [Finset.mem_singleton] using outside
    exact Function.update_of_ne different _ _
  have afterRep:=represented.preserve_small_temporary precise (by decide)
  have value:=afterHeader.value 29 (by decide)
  have selected : after.heap 29=.rational 0 := by
    simpa only [Nat.zero_add,Function.update_self] using value
  have afterPrepared : HeapList after 0 (preparedInput P fee) := by
    apply precise.heapList ready.prepared
    intro offset inside
    change offset<13 at inside
    simp only [Finset.mem_singleton]
    omega
  have afterCache : HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
    apply precise.heapList ready.cache
    intro offset _inside
    simp only [Finset.mem_singleton]
    omega
  have liveHeader : Header after 0 (fun slot=>after.heap slot) := by
    intro slot inside
    exact ⟨afterHeader.live slot inside,by simp only [Nat.zero_add]⟩
  obtain ⟨trace,head,last,chain,cost,properties,proper⟩:=actual
  have allMemory : ∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget:=
    fun state member=>⟨scalar_region_memory (properties state member).1.1,(properties state member).1.2⟩
  have scalarLive : scalarRegion⊆before.live := by
    intro address member
    have bound:=(Finset.mem_Icc.mp member).2
    have inside : address<headerWords:=by change address<48;omega
    simpa only [Nat.zero_add] using ready.header.live address inside
  have allSpace : ∀ state∈trace,workingCells state≤workingCells before := by
    intro state member
    exact (existing_region_workingCells scalarLive (allMemory state member).1).le
  have excluded : ∀ state∈trace,state.pc≠labels.solveEntry := by
    intro state member
    have bound:=(properties state member).2.2
    omega
  have noCalls:=no_solve_entry labels trace excluded
  have refinement:=PDCompute.CoreSearchLoop.refinement_of_no_entry program labels P fee callConstant trace excluded
  exact ⟨trace,after,head,last,chain,cost,pc,⟨liveHeader,afterFresh,afterPrepared,afterCache⟩,
    afterRep,selected,precise.1 28 (by decide),precise.2.2.2,precise,allMemory,
    (fun state member=>(properties state member).2),proper,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,noCalls.1,noCalls.2,refinement⟩

end RootD27.Core
