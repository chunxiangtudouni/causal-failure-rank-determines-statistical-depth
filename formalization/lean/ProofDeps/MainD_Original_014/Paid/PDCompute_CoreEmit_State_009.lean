module

public import Paid.PDCompute_CoreEmit_LowerPhase_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame

theorem stateCode_decompose (origin returnPC : ℕ) :
    stateCode origin returnPC=lowerPhaseCode origin returnPC++solveCode (origin+37) true returnPC := rfl

private theorem bracket_encoding_length (lower upper : MultiplierSolve) :
    (encodeState (.bracket lower upper)).length+1=
      (encodeTable lower.table).length+(encodeTable upper.table).length+4 := by
  simp only [encodeState,encodeSolve,List.length_append,List.length_cons]
  omega

private theorem bracket_time_bound (left right : ℕ) :
    135*left+555+(135*right+420)≤1000*(left+right+4) := by omega

/-- COMPLETE original exact/bracket state encoding, using actual tag,
actual rational prices, actual lengths and two physical retained tables.
No initialized entry register or encoded answer in code is required. -/
theorem state_trace (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (before : State) (n k M : ℕ) (state : MultiplierState)
    (position : before.pc=origin) (dimensions : PreparedDimensions before n k M)
    (payload : StatePayload before n k M state)
    (fetch : FetchesCode program origin (stateCode origin returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤1000*((encodeState state).length+1) ∧ after.pc=returnPC ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output++encodeState state ∧
      (∀ current∈trace,RootD27.Core.EmittedPrefix before (encodeState state) current) ∧
      peakCells trace≤workingCells before+(encodeState state).length := by
  have literal:=fetch
  rw [stateCode_decompose] at literal
  cases state with
  | exact solution =>
    obtain ⟨trace,after,head,last,chain,cost,pc,heap,live,output,allPrefixes,space⟩:=
      lowerPhase_trace program input origin returnPC before n k M 0 solution position dimensions payload.1 payload.2 literal.append_left
    refine ⟨trace,after,head,last,chain,?_,pc,heap,live,output,allPrefixes,space⟩
    simp only [encodeState,encodeSolve,List.length_cons]
    omega
  | bracket lower upper =>
    let earlier:=Cell.natural 1::encodeSolve lower
    let later:=encodeSolve upper
    obtain ⟨first,middle,firstHead,firstLast,firstChain,firstTime,middlePC,middleHeap,middleLive,middleOutput,firstPrefixes,_⟩:=
      lowerPhase_trace program input origin returnPC before n k M 1 lower position dimensions payload.1 payload.2.1 literal.append_left
    have atUpper : middle.pc=origin+37 := by simpa using middlePC
    have upperDimensions:=dimensions.preserve middleHeap middleLive
    have upperPayload:=payload.2.2.preserve middleHeap middleLive
    have upperFetch : FetchesCode program (origin+37) (solveCode (origin+37) true returnPC) := by
      simpa only [lowerPhase_length] using literal.append_right
    obtain ⟨second,after,secondHead,secondLast,secondChain,secondTime,afterPC,afterHeap,afterLive,afterOutput,secondPrefixes,_⟩:=
      solve_trace program input (origin+37) returnPC middle n k M true upper atUpper upperDimensions upperPayload upperFetch
    have joined:=joinTrace_spec program input first second before middle after
      (135*(encodeTable lower.table).length+555) (135*(encodeTable upper.table).length+420)
      firstHead firstLast secondHead secondLast firstChain secondChain firstTime secondTime
    have allPrefixes : ∀ current∈joinTrace first second,RootD27.Core.EmittedPrefix before (encodeState (.bracket lower upper)) current := by
      intro current member
      rcases RootD27.Core.joinTrace_member member with beforeUpper|inUpper
      · exact emitted_extend before current earlier later (firstPrefixes current beforeUpper)
      · exact emitted_prepend before middle current earlier later middleHeap middleLive middleOutput (secondPrefixes current inUpper)
    refine ⟨joinTrace first second,after,joined.1,joined.2.1,joined.2.2.1,?_,afterPC,
      afterHeap.trans middleHeap,afterLive.trans middleLive,?_,allPrefixes,
      PDLower.CalibrationCompute.peakCells_le_of_forall _ _
        (fun current member=>PDCompute.Solver.solver_emitted_workingCells (allPrefixes current member))⟩
    · rw [bracket_encoding_length]
      exact joined.2.2.2.trans (bracket_time_bound _ _)
    · rw [afterOutput,middleOutput,List.append_assoc,encodeState]

end PDCompute.CoreEmit
