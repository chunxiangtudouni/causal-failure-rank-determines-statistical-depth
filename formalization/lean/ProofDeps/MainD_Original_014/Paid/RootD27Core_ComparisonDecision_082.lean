module

public import Paid.RootD27Core_SavedMidpoint_081

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

theorem existing_region_workingCells {before after : State} {region : Finset ℕ}
    (existing : region⊆before.live) (memory : RegionMemory before after region) :
    workingCells after=workingCells before := by
  have backward : after.live⊆before.live := by
    intro address live
    rcases Finset.mem_union.mp (memory.2.1 live) with old|written
    · exact old
    · exact existing written
  have same : after.live=before.live:=Finset.Subset.antisymm backward memory.2.2.1
  unfold workingCells
  rw [same,memory.2.2.2]

def comparisonDecisionCode (comparison : Comparison) (left right zeroPC onePC : ℕ) : List Instruction :=
  comparisonStoredCode comparison left right++[.branchZero .flag zeroPC onePC]

theorem comparisonDecision_length (comparison : Comparison) (left right zeroPC onePC : ℕ) :
    (comparisonDecisionCode comparison left right zeroPC onePC).length=11 := by
  simp only [comparisonDecisionCode,List.length_append,comparisonStored_length,List.length_cons,List.length_nil]

def comparisonDecisionTarget (comparison : Comparison) (x y : ℚ) (zeroPC onePC : ℕ) : ℕ :=
  if comparison.rat x y then onePC else zeroPC

/-- Equality and risk-order tests use the actual physical fields and
their real branch instruction. The SAME execution preserves all other
heap cells, including midpoint statistics and the saved result pointer. -/
theorem represented_comparison_decision_actual (P : Parameters) (fee : ℚ) (source : MultiplierState)
    (comparison : Comparison) (left right : ℕ) (x y : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (zeroPC onePC budget callConstant : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot)) (fresh : before.register .fresh=.natural 0)
    (represented : SearchStateRep P fee before source) (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : before.heap left=.rational x) (rightValue : before.heap right=.rational y)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+11)≤budget)
    (zeroBits : natBits zeroPC≤budget) (oneBits : natBits onePC≤budget)
    (belowEntry : before.pc+11<labels.solveEntry) (zeroBelow : zeroPC<labels.solveEntry) (oneBelow : onePC<labels.solveEntry)
    (fetched : FetchesCode program before.pc (comparisonDecisionCode comparison left right zeroPC onePC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤180 ∧
      after.pc=comparisonDecisionTarget comparison x y zeroPC onePC ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ SearchStateRep P fee after source ∧
      RegionMemory before after {40} ∧
      (∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,(before.pc≤state.pc ∧ state.pc≤before.pc+10) ∨
        state.pc=comparisonDecisionTarget comparison x y zeroPC onePC) ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+11) ∧
      peakCells trace≤workingCells before ∧ actualSolveRequests labels trace=[] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 ∧
      SolverCallRefinement program labels P fee callConstant trace := by
  obtain ⟨trace,head,last,chain,cost,comparedRep,comparedHeader,comparedFresh,flag,comparedMemory,
    properties,scope,_proper,_requests,_count⟩:=
    represented_comparison_actual P fee source comparison left right x y program labels input before budget
      header fresh represented leftInside rightInside leftValue rightValue safe small addressBits
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+10≤before.pc+11)).trans pcBits) (by omega) fetched.append_left
  let compared:=comparisonStoredResult before left right (comparison.rat x y)
  let after : State:={compared with pc:=comparisonDecisionTarget comparison x y zeroPC onePC}
  have comparedPC : compared.pc=before.pc+10:=rfl
  have branchFetch : program[compared.pc]?=some (.branchZero .flag zeroPC onePC):=fetched 10 (by change 10<11;decide)
  have comparedFlag : compared.register .flag=.natural (if comparison.rat x y then 1 else 0):=flag
  have branch : step program input compared=some after := by
    cases outcome : comparison.rat x y <;>
      simp [step,branchFetch,Instruction.execute,comparedFlag,Cell.nat?,after,comparisonDecisionTarget,outcome]
  have targetBits : natBits (comparisonDecisionTarget comparison x y zeroPC onePC)≤budget := by
    unfold comparisonDecisionTarget
    split_ifs <;> assumption
  have afterSafe : RootD27.Bits.SafeBits after budget:=
    ((properties compared (List.mem_of_getLast? last)).2).withPC _ targetBits
  have joined:=chain_append_control program input trace compared after chain last branch
  have nonempty : trace≠[]:=by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at head
  have finalMemory : RegionMemory before after {40}:=comparedMemory
  have finalProperties : RegionMemory before after scalarRegion ∧ RootD27.Bits.SafeBits after budget:=
    ⟨finalMemory.enlarge (by decide),afterSafe⟩
  have allProperties : ∀ state∈trace++[after],RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget := by
    intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact properties state earlier
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact finalProperties
  have allScope : ∀ state∈trace++[after],
      (before.pc≤state.pc ∧ state.pc≤before.pc+10) ∨ state.pc=comparisonDecisionTarget comparison x y zeroPC onePC := by
    intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact Or.inl (scope state earlier)
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact Or.inr rfl
  have proper : ∀ state∈(trace++[after]).dropLast,before.pc≤state.pc ∧ state.pc<before.pc+11 := by
    intro state member
    have earlier : state∈trace:=by simpa using member
    have bounds:=scope state earlier
    omega
  have excluded : ∀ state∈trace++[after],state.pc≠labels.solveEntry := by
    intro state member
    rcases allScope state member with inline|terminal
    · omega
    · rw [terminal]
      unfold comparisonDecisionTarget
      split_ifs <;> omega
  have noCalls:=no_solve_entry labels (trace++[after]) excluded
  have refinement:=PDCompute.CoreSearchLoop.refinement_of_no_entry program labels P fee callConstant (trace++[after]) excluded
  have scalarLive : scalarRegion⊆before.live := by
    intro address member
    have bound:=(Finset.mem_Icc.mp member).2
    have inside : address<headerWords:=by change address<48;omega
    simpa only [Nat.zero_add] using header.live address inside
  have allSpace : ∀ state∈trace++[after],workingCells state≤workingCells before := by
    intro state member
    exact (existing_region_workingCells scalarLive (allProperties state member).1).le
  have afterRep : SearchStateRep P fee after source := by cases source <;> exact comparedRep
  have afterLast : (trace++[after]).getLast?=some after:=by simp
  refine ⟨trace++[after],after,?_,afterLast,joined.1,?_,rfl,comparedFresh,comparedHeader,afterRep,
    finalMemory,allProperties,allScope,proper,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,
    noCalls.1,noCalls.2,refinement⟩
  · simpa only [List.head?_append_of_ne_nil trace nonempty] using head
  · omega

end RootD27.Core
