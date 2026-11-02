module

public import Paid.RootD27Core_TagDecision_077

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

def stopDecisionTarget (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (before : State) (decrementPC : ℕ) : ℕ :=
  if P.searchStopped fee (.bracket lower upper) then decrementPC else before.pc+183

/-- The actual source stop computation and its actual branch form one
183-op inline phase. Its exact/stopped exit is a real jump to the outer
decrement, with all original cache, bracket and counter data retained. -/
theorem represented_stop_decision_actual (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (decrementPC scale budget : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot)) (fresh : before.register .fresh=.natural 0)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+183)≤budget) (decrementBits : natBits decrementPC≤budget)
    (belowEntry : before.pc+183<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (fetched : FetchesCode program before.pc (stopDecisionCode before.pc (before.pc+183) decrementPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤3015 ∧
      after.pc=stopDecisionTarget P fee lower upper before decrementPC ∧
      after.register .fresh=.natural 0 ∧ Header after 0 (fun slot=>after.heap slot) ∧
      SearchStateRep P fee after (.bracket lower upper) ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧ peakCells trace≤workingCells before ∧
      (∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,(before.pc≤state.pc ∧ state.pc≤before.pc+182) ∨
        state.pc=stopDecisionTarget P fee lower upper before decrementPC) ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+183) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 := by
  obtain ⟨trace,tested,head,last,chain,cost,testedPC,testedFresh,testedHeader,testedRep,
    testedPrepared,testedCache,flag,counter,output,space,properties,scope,_proper,_requests,_count⟩:=
    represented_stop_actual P fee lower upper program labels input before scale budget header fresh prepared stored
      represented safe intrinsic room addressBits
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+182≤before.pc+183)).trans pcBits)
      (by omega) fetched.append_left
  let after : State:={tested with pc:=stopDecisionTarget P fee lower upper before decrementPC}
  have branchFetch : program[tested.pc]?=some (.branchZero .flag (before.pc+183) decrementPC) := by
    rw [testedPC]
    exact fetched 182 (by change 182<183;decide)
  have branch : step program input tested=some after := by
    by_cases stopped : P.searchStopped fee (.bracket lower upper)
    · simp [step,branchFetch,Instruction.execute,flag,Cell.nat?,after,stopDecisionTarget,stopped]
    · simp [step,branchFetch,Instruction.execute,flag,Cell.nat?,after,stopDecisionTarget,stopped]
  have targetBits : natBits (stopDecisionTarget P fee lower upper before decrementPC)≤budget := by
    unfold stopDecisionTarget
    split_ifs <;> assumption
  have afterSafe : RootD27.Bits.SafeBits after budget:=
    ((properties tested (List.mem_of_getLast? last)).2).withPC _ targetBits
  have joined:=chain_append_control program input trace tested after chain last branch
  have nonempty : trace≠[]:=by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at head
  have finalProperties : RegionMemory before after scalarRegion ∧ RootD27.Bits.SafeBits after budget:=
    ⟨(properties tested (List.mem_of_getLast? last)).1,afterSafe⟩
  have allProperties : ∀ state∈trace++[after],RegionMemory before state scalarRegion ∧
      RootD27.Bits.SafeBits state budget := by
    intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact properties state earlier
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact finalProperties
  have allScope : ∀ state∈trace++[after],
      (before.pc≤state.pc ∧ state.pc≤before.pc+182) ∨
        state.pc=stopDecisionTarget P fee lower upper before decrementPC := by
    intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact Or.inl (scope state earlier)
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact Or.inr rfl
  have proper : ∀ state∈(trace++[after]).dropLast,before.pc≤state.pc ∧ state.pc<before.pc+183 := by
    intro state member
    have earlier : state∈trace:=by simpa using member
    have bounds:=scope state earlier
    omega
  have noCalls:=no_solve_entry labels (trace++[after]) (by
    intro state member
    rcases allScope state member with inline|terminal
    · omega
    · rw [terminal]
      unfold stopDecisionTarget
      split_ifs <;> omega)
  have testedBound:=(workingCells_le_peak_of_member trace tested (List.mem_of_getLast? last)).trans space
  have allSpace : ∀ state∈trace++[after],workingCells state≤workingCells before := by
    intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact (workingCells_le_peak_of_member trace state earlier).trans space
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact testedBound
  have afterLast : (trace++[after]).getLast?=some after:=by simp
  refine ⟨trace++[after],after,?_,afterLast,joined.1,?_,rfl,testedFresh,testedHeader,testedRep,
    testedPrepared,testedCache,counter,output,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,
    allProperties,allScope,proper,noCalls.1,noCalls.2⟩
  · simpa only [List.head?_append_of_ne_nil trace nonempty] using head
  · omega

theorem stopped_step_fixed (P : Parameters) (fee : ℚ) (source : MultiplierState)
    (stopped : P.searchStopped fee source) :
    P.cachedMultiplierStep P.endpointCache fee source=source := by
  simp only [cachedMultiplierStep,ite_eq_left stopped]

end RootD27.Core
