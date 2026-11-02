module

public import Paid.RootD27Core_SelectedState_070
public import Paid.PDLower_CoreSearch_LocatedComplete_037

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

/-- All ten actual source scalar fields come from the real prepared
input and the two retained original solves. -/
theorem original_bracket_fields (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (state : State)
    (prepared : HeapList state 0 (preparedInput P fee))
    (represented : SearchStateRep P fee state (.bracket lower upper)) :
    state.heap 3=.rational P.certificate.risk ∧ state.heap 5=.rational fee ∧
    state.heap 14=.rational lower.multiplier ∧ state.heap 15=.rational upper.multiplier ∧
    state.heap 16=.rational (P.solveRecord lower).observation ∧
    state.heap 17=.rational (P.solveRecord lower).repairs ∧ state.heap 18=.rational (P.solveRisk lower) ∧
    state.heap 19=.rational (P.solveRecord upper).observation ∧
    state.heap 20=.rational (P.solveRecord upper).repairs ∧ state.heap 21=.rational (P.solveRisk upper) := by
  have risk:=PDLower.CalibrationCompute.HeapList.value prepared 3 (by change 3<13;decide)
  have feeValue:=PDLower.CalibrationCompute.HeapList.value prepared 5 (by change 5<13;decide)
  change state.heap 3=.rational P.certificate.risk at risk
  change state.heap 5=.rational fee at feeValue
  have lowerFields:=represented.2.2.2.1.original_values represented.1
  have upperFields:=represented.2.2.2.2.original_values represented.2.1
  exact ⟨risk,feeValue,lowerFields.1,upperFields.1,lowerFields.2.1,lowerFields.2.2.1,
    lowerFields.2.2.2,upperFields.2.1,upperFields.2.2.1,upperFields.2.2.2⟩

private theorem prepared_after_scalar {P : Parameters} {fee : ℚ} {before after : State}
    (prepared : HeapList before 0 (preparedInput P fee))
    (memory : RegionMemory before after (Finset.Icc 29 42)) : HeapList after 0 (preparedInput P fee) := by
  apply memory.heapList prepared
  intro offset inside
  change offset<13 at inside
  simp only [Finset.mem_Icc]
  omega

private theorem cache_after_scalar {P : Parameters} {before after : State}
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (memory : RegionMemory before after (Finset.Icc 29 42)) :
    HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
  apply memory.heapList stored
  intro offset _inside
  simp only [Finset.mem_Icc]
  omega

/-- Source stopping test on the actual physical bracket. Original
prepared/cache/state fields are outputs of preservation, not premises
about the success of an independent test. PC and bits use the SAME run. -/
theorem represented_stop_actual (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State) (scale budget : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot)) (fresh : before.register .fresh=.natural 0)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+182)≤budget) (belowEntry : before.pc+182<labels.solveEntry)
    (fetched : FetchesCode program before.pc (bracketStopCode before.pc)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤3000 ∧
      after.pc=before.pc+182 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ SearchStateRep P fee after (.bracket lower upper) ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.register .flag=.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      peakCells trace≤workingCells before ∧
      (∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+182) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+182) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 := by
  obtain ⟨risk,feeValue,lowerPrice,upperPrice,lowerObs,lowerRep,lowerRisk,upperObs,upperRep,upperRisk⟩:=
    original_bracket_fields P fee lower upper before prepared represented
  obtain ⟨trace,after,values,head,last,chain,cost,afterHeader,_kept,afterFresh,pc,flag,_storedFlag,
    _mixture,output,low,properties,scope,proper⟩:=
    PDLower.CoreSearch.Located.bracketStop_trace_bits P fee lower upper program input before.pc before
      (fun slot=>before.heap slot) scale budget rfl header fresh risk feeValue lowerPrice upperPrice
      lowerObs lowerRep lowerRisk upperObs upperRep upperRisk safe intrinsic room addressBits pcBits fetched
  have finalProperties:=properties after (List.mem_of_getLast? last)
  have finalRegion:=scalar_final_region finalProperties.1 low
  have afterRep:=represented.preserve_low_scalars finalProperties.1 low
  have liveHeader : Header after 0 (fun slot=>after.heap slot) := by
    intro slot inside
    refine ⟨?_,by simp only [Nat.zero_add]⟩
    rw [finalProperties.1.2.2.1]
    exact header.live slot inside
  have allSpace : ∀ state∈trace,workingCells state≤workingCells before := by
    intro state member
    have fields:=(properties state member).1
    unfold workingCells
    rw [fields.2.2.1,fields.2.2.2]
  have noCalls:=no_solve_entry labels trace (by
    intro state member
    have bound:=scope state member
    omega)
  exact ⟨trace,after,head,last,chain,cost,pc,afterFresh,liveHeader,afterRep,
    prepared_after_scalar prepared finalRegion,cache_after_scalar stored finalRegion,flag,low 28 (by decide),output,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,
    (fun state member=>⟨scalar_region_memory (properties state member).1,(properties state member).2⟩),
    scope,proper,noCalls.1,noCalls.2⟩

/-- Final bracket weight is recomputed from the current two real solves,
including J=0 or the last bracket update. The source state and actual
tables survive this SAME numeric/PC/time-bounded selector run. -/
theorem represented_final_selector_actual (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State) (scale budget : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot)) (fresh : before.register .fresh=.natural 0)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+160)≤budget) (belowEntry : before.pc+160<labels.solveEntry)
    (fetched : FetchesCode program before.pc (finalBracketCode before.pc)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤3000 ∧
      after.pc=before.pc+160 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ SearchStateRep P fee after (.bracket lower upper) ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.heap 29=.rational (clipRat (P.mixtureWeight lower upper)) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      peakCells trace≤workingCells before ∧
      (∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+160) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+160) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 := by
  obtain ⟨risk,feeValue,lowerPrice,upperPrice,lowerObs,lowerRep,lowerRisk,upperObs,upperRep,upperRisk⟩:=
    original_bracket_fields P fee lower upper before prepared represented
  obtain ⟨trace,after,head,last,chain,cost,afterFresh,pc,value,output,low,properties,scope,proper⟩:=
    PDLower.CoreSearch.Located.finalBracket_trace_bits P fee lower upper program input before.pc before
      (fun slot=>before.heap slot) scale budget rfl header fresh risk feeValue lowerPrice upperPrice
      lowerObs lowerRep lowerRisk upperObs upperRep upperRisk safe intrinsic room addressBits pcBits fetched
  have finalProperties:=properties after (List.mem_of_getLast? last)
  have finalRegion:=scalar_final_region finalProperties.1 low
  have liveHeader : Header after 0 (fun slot=>after.heap slot) := by
    intro slot inside
    refine ⟨?_,by simp only [Nat.zero_add]⟩
    rw [finalProperties.1.2.2.1]
    exact header.live slot inside
  have allSpace : ∀ state∈trace,workingCells state≤workingCells before := by
    intro state member
    have fields:=(properties state member).1
    unfold workingCells
    rw [fields.2.2.1,fields.2.2.2]
  have noCalls:=no_solve_entry labels trace (by
    intro state member
    have bound:=scope state member
    omega)
  exact ⟨trace,after,head,last,chain,cost,pc,afterFresh,liveHeader,
    represented.preserve_low_scalars finalProperties.1 low,
    prepared_after_scalar prepared finalRegion,cache_after_scalar stored finalRegion,value,low 28 (by decide),output,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,
    (fun state member=>⟨scalar_region_memory (properties state member).1,(properties state member).2⟩),
    scope,proper,noCalls.1,noCalls.2⟩

end RootD27.Core
