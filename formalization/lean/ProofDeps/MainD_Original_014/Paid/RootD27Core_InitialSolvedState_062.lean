module

public import Paid.RootD27Core_HeaderSolvedCall_061

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

def initialSolvedCallsCode (origin entry : ℕ) : List Instruction :=
  headerSolvedCallCode origin entry false++headerSolvedCallCode (origin+72) entry true

theorem initialSolvedCalls_length (origin entry : ℕ) :
    (initialSolvedCallsCode origin entry).length=144 := by
  simp only [initialSolvedCallsCode,List.length_append,headerSolvedCall_length]

def initialSolvedCallsRegion (P : Parameters) (fee : ℚ) : Finset ℕ :=
  solvedBufferCallRegion P fee 0 false∪solvedBufferCallRegion P fee P.Lambda true

/-- Both source-initial solves run, return and physically retain their
actual tables. The high call preserves the low table/metadata. This
constructs the ORIGINAL cachedInitialState representation, without
supplying solved tables or a pre-existing search representation. -/
theorem initial_solved_state_actual (P : Parameters) (fee : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (values : ℕ→Cell) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0)
    (tagValue : values 13=.natural 1) (zeroValue : values 14=.rational 0)
    (lambdaValue : values 15=.rational P.Lambda)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (fetched : FetchesCode program before.pc (initialSolvedCallsCode before.pc labels.solveEntry))
    (belowEntry : before.pc+144<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤84000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=before.pc+144 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧
      SearchStateRep P fee after (P.cachedInitialState P.endpointCache fee) ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+156*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      (∀ state∈trace,RegionMemory before state (initialSolvedCallsRegion P fee)) ∧
      actualSolveRequests labels trace=[0,P.Lambda] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=2 := by
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  let region:=initialSolvedCallsRegion P fee
  change FetchesCode program before.pc
    (headerSolvedCallCode before.pc labels.solveEntry false++
      headerSolvedCallCode (before.pc+72) labels.solveEntry true) at fetched
  have lowerValue : values (multiplierSlot false)=.rational 0:=zeroValue
  obtain ⟨low,middle,lh,ll,lc,lt,middlePC,middleFresh,middleHeader,lowRep,preparedMiddle,cacheMiddle,
    middleOutput,lowPeak,lowMemory,lowRequests,lowCount⟩:=
    header_solved_call_actual P fee 0 program labels input before values false header fresh lowerValue
      prepared stored fetched.append_left (by omega) stubFetch bodyFetch
  have middleMemory:=RegionMemory.trace_last lowMemory ll
  have upperOutside : 15∉solvedBufferCallRegion P fee 0 false :=
    solvedCall_small_outside P fee 0 false 15 (by decide) (by decide) (by decide)
  have upperValue : (fun slot=>middle.heap slot) (multiplierSlot true)=.rational P.Lambda :=
    (middleMemory.1 15 upperOutside).trans ((header.value 15 (by decide)).trans lambdaValue)
  have upperFetch : FetchesCode program middle.pc (headerSolvedCallCode middle.pc labels.solveEntry true) := by
    rw [middlePC]
    simpa only [headerSolvedCall_length] using fetched.append_right
  obtain ⟨high,after,hh,hl,hc,ht,afterPC,afterFresh,afterHeader,highRep,preparedAfter,cacheAfter,
    output,highPeak,highMemory,highRequests,highCount⟩:=
    header_solved_call_actual P fee P.Lambda program labels input middle (fun slot=>middle.heap slot) true
      middleHeader middleFresh upperValue preparedMiddle cacheMiddle upperFetch (by omega) stubFetch bodyFetch
  have highFinalMemory:=RegionMemory.trace_last highMemory hl
  have lowAfter:=lowRep.preserve_other_call (by decide : (true : Bool)≠false) highFinalMemory
  have joined:=joinTrace_spec program input low high before middle after
    (42000*(P.certificate.M+1)*entries) (42000*(P.certificate.M+1)*entries) lh ll hh hl lc hc lt ht
  have allMemory : ∀ state∈joinTrace low high,RegionMemory before state region := by
    intro state member
    rcases joinTrace_member member with lowMember|highMember
    · exact (lowMemory state lowMember).enlarge Finset.subset_union_left
    · exact (middleMemory.enlarge Finset.subset_union_left).trans
        ((highMemory state highMember).enlarge Finset.subset_union_right)
  have finalMemory:=RegionMemory.trace_last allMemory joined.2.1
  have tagBefore : HeapList before 13 [.natural 1] := by
    apply PDLower.CalibrationCompute.HeapList.of_values
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      simpa only [Nat.zero_add,Nat.add_zero] using header.live 13 (by decide)
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      simpa only [Nat.zero_add,Nat.add_zero,List.getElem_cons_zero] using
        (header.value 13 (by decide)).trans tagValue
  have tagAfter : HeapList after 13 [.natural 1] := by
    apply finalMemory.heapList tagBefore
    intro offset inside
    have zero : offset=0:=by change offset<1 at inside;omega
    subst offset
    simp only [Nat.add_zero]
    intro member
    rcases Finset.mem_union.mp member with lowRegion|highRegion
    · exact solvedCall_tag_outside P fee 0 false lowRegion
    · exact solvedCall_tag_outside P fee P.Lambda true highRegion
  have represented : SearchStateRep P fee after (P.cachedInitialState P.endpointCache fee) :=
    ⟨originalSolved_cached P fee 0,originalSolved_cached P fee P.Lambda,tagAfter,lowAfter,highRep⟩
  have counter : after.heap 28=before.heap 28 := by
    apply finalMemory.1
    intro member
    rcases Finset.mem_union.mp member with lowRegion|highRegion
    · exact solvedCall_counter_outside P fee 0 false lowRegion
    · exact solvedCall_counter_outside P fee P.Lambda true highRegion
  change peakCells low≤workingCells before+78*entries at lowPeak
  change peakCells high≤workingCells middle+78*entries at highPeak
  have middleBound:=(workingCells_le_peak_of_member low middle (List.mem_of_getLast? ll)).trans lowPeak
  have allSpace : ∀ state∈joinTrace low high,workingCells state≤workingCells before+156*entries := by
    intro state member
    rcases joinTrace_member member with lowMember|highMember
    · have bound:=(workingCells_le_peak_of_member low state lowMember).trans lowPeak
      omega
    · have bound:=(workingCells_le_peak_of_member high state highMember).trans highPeak
      omega
  have noLast:=no_solve_entry labels [middle] (by
    intro state member
    have same : state=middle:=List.mem_singleton.mp member
    subst state
    omega)
  have split:=List.dropLast_append_getLast? middle (by rw [ll];simp)
  have droppedRequests : actualSolveRequests labels low.dropLast=[0] := by
    rw [←split,solveRequests_append,noLast.1,List.append_nil] at lowRequests
    exact lowRequests
  have droppedCount : PaperProofs.Paid.Computation.entryCount labels.solveEntry low.dropLast=1 := by
    rw [←split,solveEntries_append,noLast.2,Nat.add_zero] at lowCount
    exact lowCount
  have finalPC : after.pc=before.pc+144:=by omega
  have timeBudget : 42000*(P.certificate.M+1)*entries+42000*(P.certificate.M+1)*entries≤
      84000*(P.certificate.M+1)*entries:=by
    simp only [Nat.mul_assoc]
    omega
  refine ⟨joinTrace low high,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans timeBudget,
    finalPC,afterFresh,afterHeader,represented,preparedAfter,cacheAfter,counter,output.trans middleOutput,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,?_,?_⟩
  · change actualSolveRequests labels (low.dropLast++high)=[0,P.Lambda]
    rw [solveRequests_append,droppedRequests,highRequests]
    rfl
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry (low.dropLast++high)=2
    rw [solveEntries_append,droppedCount,highCount]

end RootD27.Core
