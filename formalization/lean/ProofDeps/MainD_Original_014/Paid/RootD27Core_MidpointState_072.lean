module

public import Paid.RootD27Core_SearchScalars_071

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

/-- Preserve all real source-state fields and buffers through a phase
whose physical write region avoids metadata0..23 and both buffers. -/
theorem SolvedBuffer.preserve_quiet {P : Parameters} {fee penalty : ℚ} {upper : Bool}
    {before after : State} {region : Finset ℕ} (represented : SolvedBuffer P fee penalty upper before)
    (memory : RegionMemory before after region)
    (metadataOutside : ∀ address<24,address∉region)
    (buffersOutside : ∀ side offset,
      retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools side+offset∉region) :
    SolvedBuffer P fee penalty upper after := by
  apply represented.preserve _ memory
  · intro offset inside
    apply metadataOutside
    cases upper <;> simp only [multiplierSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · intro offset inside
    apply metadataOutside
    cases upper <;> simp only [statisticsSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · intro offset inside
    apply metadataOutside
    cases upper <;> simp only [tableLengthSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · intro offset _inside
    exact buffersOutside upper offset

theorem SearchStateRep.preserve_quiet {P : Parameters} {fee : ℚ} {source : MultiplierState}
    {before after : State} {region : Finset ℕ} (represented : SearchStateRep P fee before source)
    (memory : RegionMemory before after region)
    (metadataOutside : ∀ address<24,address∉region)
    (buffersOutside : ∀ side offset,
      retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools side+offset∉region) :
    SearchStateRep P fee after source := by
  have tagKeep : ∀ value : Cell,HeapList before 13 [value]→HeapList after 13 [value] := by
    intro value stored
    apply memory.heapList stored
    intro offset inside
    change offset<1 at inside
    apply metadataOutside
    omega
  cases source with
  | exact solution =>
    obtain ⟨original,tag,buffer⟩:=represented
    exact ⟨original,tagKeep _ tag,buffer.preserve_quiet memory metadataOutside buffersOutside⟩
  | bracket lower upper =>
    obtain ⟨lowerOriginal,upperOriginal,tag,lowerBuffer,upperBuffer⟩:=represented
    exact ⟨lowerOriginal,upperOriginal,tagKeep _ tag,
      lowerBuffer.preserve_quiet memory metadataOutside buffersOutside,
      upperBuffer.preserve_quiet memory metadataOutside buffersOutside⟩

theorem SearchStateRep.preserve_small_temporary {P : Parameters} {fee : ℚ} {source : MultiplierState}
    {before after : State} {region : Finset ℕ} (represented : SearchStateRep P fee before source)
    (memory : RegionMemory before after region) (small : region⊆Finset.Icc 24 47) :
    SearchStateRep P fee after source := by
  apply represented.preserve_quiet memory
  · intro address below member
    have bounds:=Finset.mem_Icc.mp (small member)
    omega
  · intro side offset member
    have bounds:=Finset.mem_Icc.mp (small member)
    have lower:=retained_base_above_workspace (99+2*P.certificate.M) P.certificate.stages P.tools side
    unfold workspaceSize headerWords at lower
    omega

def midpointStatisticsRegion (P : Parameters) : Finset ℕ :=
  workspace (99+2*P.certificate.M) P.certificate.stages P.tools∪{25,26,27}

theorem SearchStateRep.preserve_midpoint_statistics {P : Parameters} {fee : ℚ} {source : MultiplierState}
    {before after : State} (represented : SearchStateRep P fee before source)
    (memory : RegionMemory before after (midpointStatisticsRegion P)) :
    SearchStateRep P fee after source := by
  apply represented.preserve_quiet memory
  · intro address below member
    rcases Finset.mem_union.mp member with work|statistics
    · obtain ⟨offset,_inside,equal⟩:=Finset.mem_image.mp work
      omega
    · simp only [Finset.mem_insert,Finset.mem_singleton] at statistics
      omega
  · intro side offset member
    rcases Finset.mem_union.mp member with work|statistics
    · exact retained_outside_workspace _ _ _ offset side work
    · have lower:=retained_base_above_workspace (99+2*P.certificate.M) P.certificate.stages P.tools side
      unfold workspaceSize headerWords at lower
      simp only [Finset.mem_insert,Finset.mem_singleton] at statistics
      omega

/-- Compute the actual next penalty from the source bracket. Both
original retained solutions survive; slot24 and the real total register
contain the midpoint. All numeric and PC facts belong to this one run. -/
theorem represented_midpoint_actual (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State) (scale budget : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot)) (fresh : before.register .fresh=.natural 0)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+24)≤budget) (belowEntry : before.pc+24<labels.solveEntry)
    (fetched : FetchesCode program before.pc (headerCode midpointCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤375 ∧
      after.pc=before.pc+24 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ SearchStateRep P fee after (.bracket lower upper) ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.register .total=.rational ((lower.multiplier+upper.multiplier)/2) ∧
      after.heap 24=.rational ((lower.multiplier+upper.multiplier)/2) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      peakCells trace≤workingCells before ∧ RegionMemory before after {24,39} ∧
      (∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+24) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+24) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 := by
  have fields:=original_bracket_fields P fee lower upper before prepared represented
  obtain ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,pc,total,value,output,properties,scope,proper⟩:=
    PDLower.CoreSearch.Located.midpoint_trace_bits program input before (fun slot=>before.heap slot)
      lower.multiplier upper.multiplier scale budget header fresh fields.2.2.1 fields.2.2.2.1
      safe intrinsic.lowerPrice intrinsic.upperPrice room addressBits pcBits fetched
  have finalProperties:=properties after (List.mem_of_getLast? last)
  have precise : RegionMemory before after {24,39} := by
    apply header_final_values_region _ header afterHeader finalProperties.1
    intro slot _inside outside
    have q24 : slot≠24:=by intro same;subst slot;simp at outside
    have q39 : slot≠39:=by intro same;subst slot;simp at outside
    simp only [midpointValues,Function.update_of_ne q24,Function.update_of_ne q39]
  have small : ({24,39} : Finset ℕ)⊆Finset.Icc 24 47 := by
    intro slot member
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with same|same <;> subst slot <;> decide
  have preparedAfter : HeapList after 0 (preparedInput P fee) := by
    apply precise.heapList prepared
    intro offset inside
    change offset<13 at inside
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have cacheAfter : HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
    apply precise.heapList stored
    intro offset _inside
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have counter : after.heap 28=before.heap 28 := by
    apply precise.1
    decide
  have liveHeader : Header after 0 (fun slot=>after.heap slot) := by
    intro slot inside
    exact ⟨afterHeader.live slot inside,by simp only [Nat.zero_add]⟩
  have allSpace : ∀ state∈trace,workingCells state≤workingCells before := by
    intro state member
    have memory:=(properties state member).1
    unfold workingCells
    rw [memory.2.2.1,memory.2.2.2]
  have noCalls:=no_solve_entry labels trace (by
    intro state member
    have bound:=scope state member
    omega)
  exact ⟨trace,after,head,last,chain,cost,pc,afterFresh,liveHeader,
    represented.preserve_small_temporary precise small,preparedAfter,cacheAfter,total,value,counter,output,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,precise,
    (fun state member=>⟨scalar_region_memory (properties state member).1,(properties state member).2⟩),
    scope,proper,noCalls.1,noCalls.2⟩

end RootD27.Core
