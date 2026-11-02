module
public import Paid.PDCompute_CoreBranch_Compare_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
@[expose] public section
namespace PDCompute.CoreBranch
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

structure Result (program : Program) (labels : RoutineLabels) (input : List Cell) (P : Parameters) (fee : ℚ)
    (lower upper : MultiplierSolve) (budget origin decrementPC : ℕ) (before : State) (source : MultiplierState) where
  trace : List State
  after : State
  head : trace.head?=some before
  last : trace.getLast?=some after
  chain : trace.IsChain (fun first later=>step program input first=some later)
  timeBound : time program trace≤150*(originalSolveEncoding P fee (midpointPenalty lower upper)).length+1560
  pc : after.pc=decrementPC
  ready : Ready P fee after
  represented : SearchStateRep P fee after source
  counter : after.heap 28=before.heap 28
  output : after.output=before.output
  memory : ∀ state∈trace,RegionMemory before state (branchRegion P)
  safe : ∀ state∈trace,RootD27.Bits.SafeBits state budget
  space : peakCells trace≤workingCells before+(originalSolveEncoding P fee (midpointPenalty lower upper)).length+3
  scope : ∀ state∈trace,(origin+251≤state.pc ∧ state.pc≤origin+515) ∨ state.pc=decrementPC
  proper : ∀ state∈trace.dropLast,origin+251≤state.pc ∧ state.pc<origin+516
  requests : actualSolveRequests labels trace=[]
  count : PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0
  refinement : SolverCallRefinement program labels P fee 40000 trace

def Result.change_source {program : Program} {labels : RoutineLabels} {input : List Cell} {P : Parameters} {fee : ℚ}
    {lower upper : MultiplierSolve} {budget origin decrementPC : ℕ} {before : State} {source target : MultiplierState}
    (result : Result program labels input P fee lower upper budget origin decrementPC before source)
    (equal : source=target) : Result program labels input P fee lower upper budget origin decrementPC before target := by
  subst target
  exact result

theorem finish_prefix (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (origin decrementPC budget : ℕ)
    (before middle : State) (cost : ℕ)
    (earlier : Prefix program input P fee (midpointPenalty lower upper) lower upper budget origin before middle cost)
    (costBound : cost≤360) (writeUpper isExact : Bool) (legalBranch : ¬(writeUpper=true ∧ isExact=true))
    (small : 7≤budget) (naturalRoom : 32*coreOperandBound P fee≤budget)
    (endBits : (Cell.natural (origin+516)).bits≤budget) (decrementBits : natBits decrementPC≤budget)
    (belowEntry : origin+516<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (position : origin+251≤middle.pc ∧ middle.pc+81≤origin+516)
    (fetched : FetchesCode program middle.pc (branchUpdateCode middle.pc writeUpper isExact decrementPC)) :
    Nonempty (Result program labels input P fee lower upper budget origin decrementPC before
      (updatedSourceState P fee (midpointPenalty lower upper) lower upper writeUpper isExact)) := by
  have middleSafe:=(earlier.properties middle (List.mem_of_getLast? earlier.last)).2
  have branchEndBits : (Cell.natural (middle.pc+81)).bits≤budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono position.2) 1).trans endBits
  obtain ⟨trace,after,head,last,chain,timeBound,pc,ready,rep,counter,output,memory,safe,space,scope,proper,
    _requests,_count,_refinement⟩:=
    branch_update_actual P fee (midpointPenalty lower upper) lower upper program labels input middle
      writeUpper isExact decrementPC budget 40000 legalBranch earlier.ready earlier.represented earlier.data.price
      earlier.data.statistics earlier.data.saved earlier.data.table middleSafe small naturalRoom branchEndBits decrementBits
      (by omega) decrementBelow fetched
  have joined:=joinTrace_spec program input earlier.trace trace before middle after cost
    (150*(originalSolveEncoding P fee (midpointPenalty lower upper)).length+1200)
    earlier.head earlier.last head last earlier.chain chain earlier.timeBound timeBound
  have allMemory:=RegionMemory.join_trace earlier.trace trace before middle (branchRegion P) earlier.last
    (fun state member=>((earlier.properties state member).1).enlarge (scalar_subset_branch P))
    (fun state member=>(memory state member).enlarge (update_region_subset P fee (midpointPenalty lower upper) writeUpper))
  have allSafe:=PDCompute.Pack.joinTrace_invariant earlier.trace trace
    (fun state=>RootD27.Bits.SafeBits state budget) (fun state member=>(earlier.properties state member).2) safe
  have middleSpace:=(workingCells_le_peak_of_member earlier.trace middle (List.mem_of_getLast? earlier.last)).trans earlier.space
  have allSpace : ∀ state∈joinTrace earlier.trace trace,
      workingCells state≤workingCells before+(originalSolveEncoding P fee (midpointPenalty lower upper)).length+3 := by
    intro state member
    rcases joinTrace_member member with early|late
    · have bound:=(workingCells_le_peak_of_member earlier.trace state early).trans earlier.space
      omega
    · have bound:=(workingCells_le_peak_of_member trace state late).trans space
      omega
  have allScope : ∀ state∈joinTrace earlier.trace trace,
      (origin+251≤state.pc ∧ state.pc≤origin+515) ∨ state.pc=decrementPC := by
    intro state member
    rcases joinTrace_member member with early|late
    · exact Or.inl (earlier.scope state early)
    · rcases scope state late with inline|terminal
      · exact Or.inl ⟨by omega,by omega⟩
      · exact Or.inr terminal
  have nonempty : trace≠[]:=by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at head
  have allProper : ∀ state∈(joinTrace earlier.trace trace).dropLast,origin+251≤state.pc ∧ state.pc<origin+516 := by
    intro state member
    change state∈(earlier.trace.dropLast++trace).dropLast at member
    rw [List.dropLast_append_of_ne_nil nonempty] at member
    rcases List.mem_append.mp member with early|late
    · have bound:=earlier.scope state (List.mem_of_mem_dropLast early)
      omega
    · have bound:=proper state late
      omega
  have excluded : ∀ state∈joinTrace earlier.trace trace,state.pc≠labels.solveEntry := by
    intro state member
    rcases allScope state member with inline|terminal <;> omega
  have noCalls:=no_solve_entry labels (joinTrace earlier.trace trace) excluded
  have refinement:=refinement_of_no_entry program labels P fee 40000 (joinTrace earlier.trace trace) excluded
  refine ⟨⟨joinTrace earlier.trace trace,after,joined.1,joined.2.1,joined.2.2.1,?_,pc,ready,rep,
    counter.trans (earlier.frame.1 28 (by decide)),output.trans earlier.frame.2.2.2,allMemory,allSafe,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allScope,allProper,noCalls.1,noCalls.2,refinement⟩⟩
  exact joined.2.2.2.trans (by omega)

end PDCompute.CoreBranch
