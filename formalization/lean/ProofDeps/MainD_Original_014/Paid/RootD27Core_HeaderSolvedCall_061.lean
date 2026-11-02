module

public import Paid.RootD27Core_PenaltyLoad_060

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList loadSlot loadSlotResult)

def headerSolvedCallCode (origin entry : ℕ) (upper : Bool) : List Instruction :=
  loadSlot (multiplierSlot upper) .total++solvedBufferCallCode (origin+3) entry upper

theorem headerSolvedCall_length (origin entry : ℕ) (upper : Bool) :
    (headerSolvedCallCode origin entry upper).length=72 := by
  simp only [headerSolvedCallCode,List.length_append,solvedBufferCall_length]
  rfl

/-- A physical heap penalty load and the complete original solve/retain
call are ONE actual trace. There is no penalty-register input premise. -/
theorem header_solved_call_actual (P : Parameters) (fee penalty : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (values : ℕ→Cell) (upper : Bool) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0)
    (lambdaValue : values (multiplierSlot upper)=.rational penalty)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (fetched : FetchesCode program before.pc (headerSolvedCallCode before.pc labels.solveEntry upper))
    (belowEntry : before.pc+72<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤42000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=before.pc+72 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ SolvedBuffer P fee penalty upper after ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+78*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      (∀ state∈trace,RegionMemory before state (solvedBufferCallRegion P fee penalty upper)) ∧
      actualSolveRequests labels trace=[penalty] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 := by
  let loaded:=loadSlotResult before 0 (multiplierSlot upper) .total
  let region:=solvedBufferCallRegion P fee penalty upper
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  change FetchesCode program before.pc
    (loadSlot (multiplierSlot upper) .total++solvedBufferCallCode (before.pc+3) labels.solveEntry upper) at fetched
  have inside : multiplierSlot upper<headerWords:=by cases upper <;> decide
  obtain ⟨load,lh,ll,lc,lt,penaltyLoaded,freshLoaded,loadMemory,loadScope⟩:=
    header_penalty_load_actual program input before values (multiplierSlot upper) penalty header inside fresh
      lambdaValue fetched.append_left
  have loadedPC : loaded.pc=before.pc+3:=rfl
  have callFetch : FetchesCode program loaded.pc (solvedBufferCallCode loaded.pc labels.solveEntry upper) := by
    change FetchesCode program (before.pc+3) (solvedBufferCallCode (before.pc+3) labels.solveEntry upper)
    exact fetched.append_right
  obtain ⟨call,after,ch,cl,cc,ct,afterPC,afterFresh,afterHeader,represented,preparedAfter,cacheAfter,
    output,callPeak,callMemory,requests,count⟩:=
    solved_buffer_call_actual P fee penalty program labels input loaded values upper
      (header.loadSlot_preserves (multiplierSlot upper) .total) lambdaValue penaltyLoaded prepared stored
      callFetch (by omega) stubFetch bodyFetch
  change peakCells call≤workingCells before+78*entries at callPeak
  have joined:=joinTrace_spec program input load call before loaded after 60
    (41000*(P.certificate.M+1)*entries) lh ll ch cl lc cc lt ct
  have loadedMemory : RegionMemory before loaded region:=RegionMemory.refl before region
  have allMemory : ∀ state∈joinTrace load call,RegionMemory before state region := by
    intro state member
    rcases joinTrace_member member with loadMember|callMember
    · have fields:=loadMemory state loadMember
      refine ⟨fun address _outside=>congrFun fields.1 address,?_,?_,fields.2.2⟩
      · rw [fields.2.1]
        exact Finset.subset_union_left
      · rw [fields.2.1]
    · exact loadedMemory.trans (callMemory state callMember)
  have allSpace : ∀ state∈joinTrace load call,workingCells state≤workingCells before+78*entries := by
    intro state member
    rcases joinTrace_member member with loadMember|callMember
    · have fields:=loadMemory state loadMember
      have same : workingCells state=workingCells before:=by
        unfold workingCells
        rw [fields.2.1,fields.2.2]
      omega
    · exact (workingCells_le_peak_of_member call state callMember).trans callPeak
  have noLoad:=no_solve_entry labels load.dropLast (by
    intro state member
    have scope:=loadScope state (List.mem_of_mem_dropLast member)
    omega)
  have positive : 0<entries:=retained_capacity_positive P.certificate.stages P.tools
  have factor : entries≤(P.certificate.M+1)*entries:=by nlinarith
  have timeBudget : 60+41000*(P.certificate.M+1)*entries≤42000*(P.certificate.M+1)*entries := by
    simp only [Nat.mul_assoc]
    omega
  refine ⟨joinTrace load call,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans timeBudget,
    by omega,afterFresh,afterHeader,represented,preparedAfter,cacheAfter,output,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,?_,?_⟩
  · change actualSolveRequests labels (load.dropLast++call)=[penalty]
    rw [solveRequests_append,noLoad.1,requests,List.nil_append]
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry (load.dropLast++call)=1
    rw [solveEntries_append,noLoad.2,count,Nat.zero_add]

end RootD27.Core
