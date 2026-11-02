module

public import Paid.RootD27Core_LivePrefix_086
public import Paid.PDCompute_CoreBranch_Actual_004
public import Paid.PDCompute_CoreGlobalBudget_Polynomial_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch PDCompute.CoreSearchLoop

/-- One physical region for every original search round. Its size has no
factor J and includes both reused retained buffers and the solver work. -/
def coreSearchRegion (P : Parameters) : Finset ℕ :=
  PDCompute.CoreMemory.globalRegion P.certificate.M P.certificate.stages P.tools

theorem scalar_subset_coreSearch (P : Parameters) : scalarRegion⊆coreSearchRegion P := by
  intro address member
  have bounds:=Finset.mem_Icc.mp member
  apply (mem_cellRegion_iff 0 _ address).mpr
  unfold PDCompute.CoreMemory.globalSpan PDCompute.CoreMemory.coreBase
  omega

theorem midpoint_subset_coreSearch (P : Parameters) :
    PDCompute.CoreMidpoint.midpointRegion P⊆coreSearchRegion P := by
  apply Finset.union_subset
  · apply Finset.union_subset
    · exact scalar_subset_coreSearch P
    · apply Finset.union_subset
      · exact PDCompute.CoreMemory.solverWorkspace_subset_global
          P.certificate.M P.certificate.stages P.tools
      · intro address member
        apply scalar_subset_coreSearch P
        simp only [Finset.mem_insert,Finset.mem_singleton] at member
        change address∈Finset.Icc 13 42
        rcases member with rfl|rfl|rfl <;> decide
  · exact PDCompute.CoreMemory.copySlots_subset_global P.certificate.M P.certificate.stages P.tools

theorem branch_subset_coreSearch (P : Parameters) :
    PDCompute.CoreBranch.branchRegion P⊆coreSearchRegion P := by
  apply Finset.union_subset
  · exact Finset.union_subset (scalar_subset_coreSearch P)
      (PDCompute.CoreMemory.copySlots_subset_global P.certificate.M P.certificate.stages P.tools)
  · exact Finset.union_subset
      (PDCompute.CoreMemory.retainedBuffer_subset_global P.certificate.M P.certificate.stages P.tools false)
      (PDCompute.CoreMemory.retainedBuffer_subset_global P.certificate.M P.certificate.stages P.tools true)

/-- The complete ORIGINAL516 body on a nonstopped bracket. The true
251 prefix is joined to the true equality/less/update suffix. Its one
solver call, fixed return-marker window and all bit/space bounds concern
this SAME trace; the update direction is computed from physical risk. -/
theorem bisection_live_actual (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (decrementPC scale budget : ℕ) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (running : ¬P.searchStopped fee (.bracket lower upper))
    (safe : RootD27.Bits.SafeBits before budget) (small : 7≤budget)
    (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (endBits : (Cell.natural (before.pc+516)).bits≤budget)
    (decrementBits : natBits decrementPC≤budget)
    (naturalRoom : 32*coreOperandBound P fee≤budget)
    (controlRoom : PDLower.CoreRuntimeNumeric.runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (scalarRoom : 4194304*solverBitScale P fee ((lower.multiplier+upper.multiplier)/2)
      P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=PDLower.CoreRuntimeNumeric.commonSolverMarkerPC labels)
    (belowEntry : before.pc+516<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (fetched : FetchesCode program before.pc (bisectionBodyCode before.pc labels.solveEntry decrementPC))
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤50000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=decrementPC ∧ Ready P fee after ∧
      SearchStateRep P fee after (P.cachedMultiplierStep P.endpointCache fee (.bracket lower upper)) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (coreSearchRegion P)) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      peakCells trace≤workingCells before+(coreSearchRegion P).card ∧
      actualSolveRequests labels trace=[(lower.multiplier+upper.multiplier)/2] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 ∧
      SolverCallRefinement program labels P fee 40000 trace := by
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  obtain ⟨front,middle,fh,fl,fc,ft,middlePC,middleReady,middleRep,price,statistics,table,descriptor,
    middleCounter,middleOutput,_frontSpace,frontMemory,frontSafe,frontRequests,_frontCount,frontCalls⟩:=
    bisection_live_prefix_actual P fee lower upper program labels input before decrementPC scale budget ready
      represented running safe small intrinsic room addressBits baseBits endBits decrementBits controlRoom scalarRoom
      markerLabel belowEntry decrementBelow fetched stubFetch bodyFetch
  have data : PDCompute.CoreBranch.MidpointData P fee
      (PDCompute.CoreBranch.midpointPenalty lower upper) middle := ⟨price,statistics,descriptor,table⟩
  obtain ⟨back,after,bh,bl,bc,bt,afterPC,afterReady,afterRep,counter,output,backMemory,backSafe,
    _backSpace,_backScope,_backProper,backRequests,_backCount,backCalls⟩:=
    PDCompute.CoreBranch.suffix_actual P fee lower upper program labels input before.pc decrementPC middle budget
      middlePC middleReady middleRep data (frontSafe middle (List.mem_of_getLast? fl)) small naturalRoom
      endBits decrementBits belowEntry decrementBelow fetched
  have joined:=joinTrace_spec program input front back before middle after
    (43000*(P.certificate.M+1)*entries) (5000*entries+2000) fh fl bh bl fc bc ft bt
  have memory:=RegionMemory.join_trace front back before middle (coreSearchRegion P) fl
    (fun state member=>(frontMemory state member).enlarge (midpoint_subset_coreSearch P))
    (fun state member=>(backMemory state member).enlarge (branch_subset_coreSearch P))
  have bits:=PDCompute.Pack.joinTrace_invariant front back (fun state=>RootD27.Bits.SafeBits state budget)
    frontSafe backSafe
  have calls:=refinement_join program labels P fee 40000 front back middle fl bh frontCalls backCalls
  have requests : actualSolveRequests labels (joinTrace front back)=[(lower.multiplier+upper.multiplier)/2] := by
    rw [requests_join labels front back middle fl (by omega),frontRequests,backRequests,List.append_nil]
  have count : PaperProofs.Paid.Computation.entryCount labels.solveEntry (joinTrace front back)=1 := by
    rw [entries_eq_requests program labels P fee 40000 _ calls,requests]
    rfl
  have finalRep : SearchStateRep P fee after
      (P.cachedMultiplierStep P.endpointCache fee (.bracket lower upper)) := by
    simp only [cachedMultiplierStep,ite_eq_right running]
    exact afterRep
  have positive : 0<entries := by unfold entries PDCompute.Solver.entryCount;positivity
  have entriesBound : entries≤(P.certificate.M+1)*entries := by nlinarith
  have cost : 43000*(P.certificate.M+1)*entries+(5000*entries+2000)≤
      50000*(P.certificate.M+1)*entries := by
    simp only [Nat.mul_assoc]
    omega
  refine ⟨joinTrace front back,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans cost,
    afterPC,afterReady,finalRep,counter.trans middleCounter,output.trans middleOutput,memory,bits,?_,
    requests,count,calls⟩
  exact PDLower.CalibrationCompute.peakCells_le_of_forall _ _
    (fun state member=>(memory state member).workingCells_le)

end RootD27.Core
