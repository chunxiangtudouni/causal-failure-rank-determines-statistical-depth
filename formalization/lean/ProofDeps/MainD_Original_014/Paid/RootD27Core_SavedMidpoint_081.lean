module

public import Paid.RootD27Core_NoSolveBody_080

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- The live Header48 already owns both actual descriptor slots. Saving
the real returned address/count cannot allocate a new live heap cell. -/
theorem save_region_no_allocation (before state : State)
    (header : Header before 0 (fun slot=>before.heap slot))
    (memory : RegionMemory before state {46,47}) : workingCells state=workingCells before := by
  have regionLive : ({46,47}:Finset ℕ)⊆before.live := by
    intro address member
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with same|same
    · subst address
      exact header.live 46 (by decide)
    · subst address
      exact header.live 47 (by decide)
  have backward : state.live⊆before.live := by
    intro address live
    rcases Finset.mem_union.mp (memory.2.1 live) with old|written
    · exact old
    · exact regionLive written
  have same : state.live=before.live:=Finset.Subset.antisymm backward memory.2.2.1
  unfold workingCells
  rw [same,memory.2.2.2]

/-- Five genuine save/reset instructions after the actual midpoint solve.
The returned table, original source bracket, midpoint and statistics all
remain physical outputs of the SAME execution, at the SAME global B. -/
theorem saved_midpoint_actual (P : Parameters) (fee penalty : ℚ) (source : MultiplierState)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State) (budget : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot))
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (represented : SearchStateRep P fee before source)
    (middlePrice : before.heap 24=.rational penalty)
    (statistics : HeapList before 25 (originalStatistics P fee penalty))
    (address : before.register .address=.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools))
    (index : before.register .index=.natural (originalSolveEncoding P fee penalty).length)
    (table : HeapList before (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
      (originalSolveEncoding P fee penalty))
    (safe : RootD27.Bits.SafeBits before budget) (small : 7≤budget)
    (pcBits : natBits (before.pc+5)≤budget) (belowEntry : before.pc+5<labels.solveEntry)
    (fetched : FetchesCode program before.pc saveSolverResultCode) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤90 ∧
      after.pc=before.pc+5 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ SearchStateRep P fee after source ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.heap 24=.rational penalty ∧ HeapList after 25 (originalStatistics P fee penalty) ∧
      HeapList after (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
        (originalSolveEncoding P fee penalty) ∧
      HeapList after 46 [.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools),
        .natural (originalSolveEncoding P fee penalty).length] ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state {46,47} ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+5) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+5) ∧ peakCells trace≤workingCells before ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 := by
  let sourceBase:=resultBase (99+2*P.certificate.M) P.certificate.stages P.tools
  let cells:=originalSolveEncoding P fee penalty
  let after:=saveSolverResult before sourceBase cells.length
  obtain ⟨trace,head,last,chain,cost,saved,fresh,output,properties,scope,proper,_space⟩:=
    PDLower.CoreRuntimeNumeric.save_resources program input before sourceBase cells.length budget
      address index safe small pcBits fetched
  have finalMemory:= (properties after (List.mem_of_getLast? last)).1
  have afterRep:=represented.preserve_small_temporary finalMemory (by
    intro address member
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    exact Finset.mem_Icc.mpr (by omega))
  have afterHeader : Header after 0 (fun slot=>after.heap slot) := by
    intro slot inside
    exact ⟨finalMemory.2.2.1 (header.live slot inside),by simp only [Nat.zero_add]⟩
  have afterPrepared : HeapList after 0 (preparedInput P fee) := by
    apply finalMemory.heapList prepared
    intro offset inside
    change offset<13 at inside
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have afterCache : HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
    apply finalMemory.heapList stored
    intro offset _inside
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have afterPrice : after.heap 24=.rational penalty:=
    (finalMemory.1 24 (by decide)).trans middlePrice
  have afterStatistics : HeapList after 25 (originalStatistics P fee penalty) := by
    apply finalMemory.heapList statistics
    intro offset inside
    change offset<3 at inside
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have afterTable : HeapList after sourceBase cells := by
    apply finalMemory.heapList table
    intro offset _inside
    have lower : 51≤sourceBase:=dense_result_source_bound _ _ _
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have counter : after.heap 28=before.heap 28:=finalMemory.1 28 (by decide)
  have allSpace : ∀ state∈trace,workingCells state≤workingCells before := by
    intro state member
    exact (save_region_no_allocation before state header (properties state member).1).le
  have noCalls:=no_solve_entry labels trace (by
    intro state member
    have bounds:=scope state member
    omega)
  exact ⟨trace,after,head,last,chain,cost,rfl,fresh,afterHeader,afterRep,afterPrepared,afterCache,
    afterPrice,afterStatistics,afterTable,saved,counter,output,properties,scope,proper,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,noCalls.1,noCalls.2⟩

end RootD27.Core
