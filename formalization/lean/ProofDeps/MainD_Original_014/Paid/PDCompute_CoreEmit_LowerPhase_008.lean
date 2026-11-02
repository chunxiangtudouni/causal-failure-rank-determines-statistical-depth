module

public import Paid.PDCompute_CoreEmit_Solve_005
public import Paid.PDCompute_CoreEmit_Guard_006
public import Paid.PDCompute_CoreEmit_HeapTransport_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (HeapList)

def lowerPhaseCode (origin returnPC : ℕ) : List Instruction:=
  outputSlotCode 13++solveCode (origin+3) false (origin+34)++stateGuardCode (origin+37) returnPC

theorem lowerPhase_length (origin returnPC : ℕ) : (lowerPhaseCode origin returnPC).length=37:=rfl

/-- True tag output, true lower solve output, and a genuine reread/branch.
This actual prefix is shared by exact and bracket without inventing a
semantic branch result or an answer-specific instruction. -/
theorem lowerPhase_trace (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (before : State) (n k M tag : ℕ) (solution : MultiplierSolve)
    (position : before.pc=origin) (dimensions : PreparedDimensions before n k M)
    (tagStored : HeapList before 13 [.natural tag]) (payload : SolvePayload before n k M false solution)
    (fetch : FetchesCode program origin (lowerPhaseCode origin returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤135*(encodeTable solution.table).length+555 ∧
      after.pc=(if tag=0 then returnPC else origin+37) ∧ after.heap=before.heap ∧ after.live=before.live ∧
      after.output=before.output++(.natural tag::encodeSolve solution) ∧
      (∀ state∈trace,RootD27.Core.EmittedPrefix before (.natural tag::encodeSolve solution) state) ∧
      peakCells trace≤workingCells before+(.natural tag::encodeSolve solution).length := by
  let tagged:=outputSlotResult before 13 (.natural tag)
  let cells:=Cell.natural tag::encodeSolve solution
  have literal:=fetch
  rw [lowerPhaseCode] at literal
  have tagFetch : FetchesCode program before.pc (outputSlotCode 13) := by rw [position];exact literal.append_left.append_left
  obtain ⟨tagTrace,tagHead,tagLast,tagChain,tagTime,tagPrefixes⟩:=
    outputSlot_trace program input before 13 (.natural tag) tagStored tagFetch
  have lowerFetch : FetchesCode program (origin+3) (solveCode (origin+3) false (origin+34)) := by
    simpa only [outputSlot_length] using literal.append_left.append_right
  have taggedAt : tagged.pc=origin+3 := by change before.pc+3=origin+3;rw [position]
  obtain ⟨lower,solved,lowerHead,lowerLast,lowerChain,lowerTime,solvedPC,solvedHeap,solvedLive,solvedOutput,lowerPrefixes,_⟩:=
    solve_trace program input (origin+3) (origin+34) tagged n k M false solution taggedAt dimensions payload lowerFetch
  have guardFetch : FetchesCode program (origin+34) (stateGuardCode ((origin+34)+3) returnPC) := by
    simpa only [List.length_append,outputSlot_length,solve_length] using literal.append_right
  have tagStill : HeapList solved 13 [.natural tag]:=heapList_same tagStored solvedHeap solvedLive
  obtain ⟨guarded,after,guardHead,guardLast,guardChain,guardTime,afterPC,afterHeap,afterLive,afterOutput,guardMemory⟩:=
    guard_trace program input (origin+34) returnPC solved tag solvedPC tagStill guardFetch
  have first:=joinTrace_spec program input tagTrace lower before tagged solved 60 (135*(encodeTable solution.table).length+420)
    tagHead tagLast lowerHead lowerLast tagChain lowerChain tagTime lowerTime
  have joined:=joinTrace_spec program input (joinTrace tagTrace lower) guarded before solved after
    (60+(135*(encodeTable solution.table).length+420)) 75 first.1 first.2.1 guardHead guardLast first.2.2.1 guardChain first.2.2.2 guardTime
  have allPrefixes : ∀ state∈joinTrace (joinTrace tagTrace lower) guarded,RootD27.Core.EmittedPrefix before cells state := by
    intro state member
    rcases RootD27.Core.joinTrace_member member with earlier|branching
    · rcases RootD27.Core.joinTrace_member earlier with tagging|solving
      · exact emitted_extend before state [.natural tag] (encodeSolve solution) (tagPrefixes state tagging).1
      · exact emitted_prepend before tagged state [.natural tag] (encodeSolve solution) rfl rfl rfl (lowerPrefixes state solving)
    · have memory:=guardMemory state branching
      apply emitted_complete before state cells (memory.1.trans solvedHeap) (memory.2.1.trans solvedLive)
      rw [memory.2.2,solvedOutput]
      change (before.output++[.natural tag])++encodeSolve solution=before.output++([.natural tag]++encodeSolve solution)
      exact List.append_assoc _ _ _
  refine ⟨joinTrace (joinTrace tagTrace lower) guarded,after,joined.1,joined.2.1,joined.2.2.1,?_,?_,
    afterHeap.trans solvedHeap,afterLive.trans solvedLive,?_,allPrefixes,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _
      (fun state member=>PDCompute.Solver.solver_emitted_workingCells (allPrefixes state member))⟩
  · exact joined.2.2.2.trans_eq (by ring)
  · exact afterPC
  · rw [afterOutput,solvedOutput]
    change (before.output++[.natural tag])++encodeSolve solution=before.output++([.natural tag]++encodeSolve solution)
    exact List.append_assoc _ _ _

end PDCompute.CoreEmit
