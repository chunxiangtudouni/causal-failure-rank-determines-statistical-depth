module

public import Paid.RootD27Core_UpdateFrame_076
public import Paid.PDLower_CoreRuntimeNumeric_SaveMetadata_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList loadSlot loadSlotResult)
open PDROC.CalibrationRow.Operand

def sourceTag : MultiplierState→ℕ
  | .exact _=>0
  | .bracket _ _=>1

theorem SearchStateRep.tag_value {P : Parameters} {fee : ℚ} {source : MultiplierState}
    {state : State} (represented : SearchStateRep P fee state source) :
    state.heap 13=.natural (sourceTag source) := by
  cases source with
  | exact solution =>
    exact PDLower.CalibrationCompute.HeapList.value represented.2.1 0 (by change 0<1;decide)
  | bracket lower upper =>
    exact PDLower.CalibrationCompute.HeapList.value represented.2.2.1 0 (by change 0<1;decide)

def tagDecisionTarget (before : State) (source : MultiplierState) (decrementPC : ℕ) : ℕ :=
  if sourceTag source=0 then decrementPC else before.pc+4

def tagDecisionResult (before : State) (source : MultiplierState) (decrementPC : ℕ) : State :=
  {loadSlotResult before 0 13 .flag with pc:=tagDecisionTarget before source decrementPC}

/-- Four real fetched instructions inspect the physically stored source
tag. An exact state really jumps to the outer decrement, while a bracket
really continues at the stop code. No storage or source state changes. -/
theorem represented_tag_actual (P : Parameters) (fee : ℚ) (source : MultiplierState)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (decrementPC budget : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot)) (fresh : before.register .fresh=.natural 0)
    (represented : SearchStateRep P fee before source) (safe : RootD27.Bits.SafeBits before budget)
    (small : 7≤budget) (pcBits : natBits (before.pc+4)≤budget) (decrementBits : natBits decrementPC≤budget)
    (belowEntry : before.pc+4<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (fetched : FetchesCode program before.pc (tagDecisionCode before.pc decrementPC)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (tagDecisionResult before source decrementPC) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤75 ∧
      Header (tagDecisionResult before source decrementPC) 0 (fun slot=>before.heap slot) ∧
      (tagDecisionResult before source decrementPC).register .fresh=.natural 0 ∧
      SearchStateRep P fee (tagDecisionResult before source decrementPC) source ∧
      (∀ state∈trace,RegionMemory before state ∅ ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,(before.pc≤state.pc ∧ state.pc≤before.pc+3) ∨
        state.pc=tagDecisionTarget before source decrementPC) ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+4) ∧
      peakCells trace≤workingCells before ∧ actualSolveRequests labels trace=[] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 := by
  let loaded:=loadSlotResult before 0 13 .flag
  let after:=tagDecisionResult before source decrementPC
  have live : 0+13∈before.live:=header.live 13 (by decide)
  have run:=PDLower.CalibrationCompute.loadSlot_execute input before 0 13 .flag fresh live
  have fetchLoad : FetchesCode program before.pc (loadSlot 13 .flag):=fetched.append_left
  have addressBits : 1+natBits (0+13)≤budget:= (show 1+natBits (0+13)≤7 by decide).trans small
  have loadBits : natBits (before.pc+3)≤budget:=
    (PDROC.DataBits.natBits_mono (by omega : before.pc+3≤before.pc+4)).trans pcBits
  obtain ⟨trace,head,last,chain,cost,properties,location,_proper,_space⟩:=
    PDLower.CoreRuntimeNumeric.linear_resources program input (loadSlot 13 .flag) before loaded ∅ budget
      (loadSlot_straight 13 .flag) fetchLoad run
      (by
        intro count bounded state executed
        have memory:=loadSlot_prefix_memory input before state 0 13 .flag fresh live count bounded executed
        exact RegionMemory.of_unchanged ∅ memory.1 memory.2.1 memory.2.2)
      (PrefixSafe.loadSlot input before 0 13 budget .flag safe fresh live addressBits loadBits)
  have loadCost : time program trace≤60:=cost
  have loadLocation : ∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+3:=location
  have loadedPC : loaded.pc=before.pc+3:=rfl
  have branchFetch : program[loaded.pc]?=some (.branchZero .flag decrementPC (before.pc+4)) :=
    fetched 3 (by change 3<4;decide)
  have loadedFlag : loaded.register .flag=.natural (sourceTag source) := by
    simpa only [loaded,loadSlotResult,Function.update_self,Nat.zero_add] using represented.tag_value
  have branch : step program input loaded=some after := by
    simp [step,branchFetch,Instruction.execute,loadedFlag,Cell.nat?,after,tagDecisionResult,tagDecisionTarget,loaded]
  have targetBits : natBits (tagDecisionTarget before source decrementPC)≤budget := by
    unfold tagDecisionTarget
    split_ifs <;> assumption
  have afterSafe : RootD27.Bits.SafeBits after budget :=
    ((properties loaded (List.mem_of_getLast? last)).2).withPC _ targetBits
  have joined:=chain_append_control program input trace loaded after chain last branch
  have nonempty : trace≠[]:=by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at head
  have finalProperties : RegionMemory before after ∅ ∧ RootD27.Bits.SafeBits after budget :=
    ⟨(properties loaded (List.mem_of_getLast? last)).1,afterSafe⟩
  have allProperties : ∀ state∈trace++[after],RegionMemory before state ∅ ∧ RootD27.Bits.SafeBits state budget := by
    intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact properties state earlier
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact finalProperties
  have allLocation : ∀ state∈trace++[after],
      (before.pc≤state.pc ∧ state.pc≤before.pc+3) ∨ state.pc=tagDecisionTarget before source decrementPC := by
    intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact Or.inl (loadLocation state earlier)
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact Or.inr rfl
  have noCalls:=no_solve_entry labels (trace++[after]) (by
    intro state member
    rcases allLocation state member with inline|terminal
    · omega
    · rw [terminal]
      unfold tagDecisionTarget
      split_ifs <;> omega)
  have proper : ∀ state∈(trace++[after]).dropLast,before.pc≤state.pc ∧ state.pc<before.pc+4 := by
    intro state member
    have earlier : state∈trace:=by simpa using member
    have bound:=loadLocation state earlier
    omega
  have afterHeader : Header after 0 (fun slot=>before.heap slot):=header
  have afterFresh : after.register .fresh=.natural 0 := by
    change (Function.update (Function.update before.register .address (.natural (0+13))) .flag
      (before.heap (0+13))) .fresh=.natural 0
    simp [fresh]
  have afterRep : SearchStateRep P fee after source := by
    cases source <;> exact represented
  have allSpace : ∀ state∈trace++[after],workingCells state≤workingCells before := by
    intro state member
    have memory:=(allProperties state member).1
    have bound:=memory.workingCells_le
    simpa only [Finset.card_empty,Nat.add_zero] using bound
  have afterLast : (trace++[after]).getLast?=some after:=by simp
  refine ⟨trace++[after],?_,afterLast,joined.1,?_,afterHeader,afterFresh,afterRep,allProperties,
    allLocation,proper,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,noCalls.1,noCalls.2⟩
  · simpa only [List.head?_append_of_ne_nil trace nonempty] using head
  · omega

theorem exact_step_fixed (P : Parameters) (fee : ℚ) (solution : MultiplierSolve) :
    P.cachedMultiplierStep P.endpointCache fee (.exact solution)=.exact solution := by
  unfold cachedMultiplierStep
  split_ifs <;> rfl

end RootD27.Core
