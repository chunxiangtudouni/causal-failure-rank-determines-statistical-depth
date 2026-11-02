module

public import Paid.PDCompute_CoreEmit_BlockBits_013
public import Paid.PDCompute_Pack_BitBudget_057
public import Common.ROOT_ActualTrace_Resources_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDROC.DataBits
open PDLower.CalibrationCompute (HeapList)

/-- Independently computed original physical ends, not a trace/resource
oracle and not a newqualification on the original input. -/
def StateEndBound (n k M cap : ℕ) : MultiplierState→Prop
  | .exact solution => bufferBase n k M false+(encodeTable solution.table).length≤cap
  | .bracket lower upper => bufferBase n k M false+(encodeTable lower.table).length≤cap ∧
      bufferBase n k M true+(encodeTable upper.table).length≤cap

private theorem lower_cap_ge99 (n k M count cap : ℕ) (bound : bufferBase n k M false+count≤cap) : 99≤cap := by
  unfold bufferBase RootD27.Core.retainedTableBase at bound
  simp only [Bool.false_eq_true,ite_false] at bound
  omega

/-- Actual shared37-op prefix on SAME B, including the true tagbranch. -/
theorem lowerPhase_trace_bits (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (before : State) (n k M tag cap budget : ℕ) (solution : MultiplierSolve)
    (position : before.pc=origin) (dimensions : PreparedDimensions before n k M)
    (tagStored : HeapList before 13 [.natural tag]) (payload : SolvePayload before n k M false solution)
    (safe : RootD27.Bits.SafeBits before budget)
    (endBound : bufferBase n k M false+(encodeTable solution.table).length≤cap)
    (capBits : 1+natBits cap≤budget) (counter : natBits (origin+37)≤budget) (returnBits : natBits returnPC≤budget)
    (fetch : FetchesCode program origin (lowerPhaseCode origin returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      after.pc=(if tag=0 then returnPC else origin+37) ∧ after.heap=before.heap ∧ after.live=before.live ∧
      ∀ state∈trace,RootD27.Bits.SafeBits state budget := by
  let tagged:=outputSlotResult before 13 (.natural tag)
  have fixedCap:=lower_cap_ge99 n k M _ cap endBound
  have tagBits : 1+natBits 13≤budget:=
    (Nat.add_le_add_left (natBits_mono (by omega : 13≤cap)) 1).trans capBits
  have tagPC : natBits (before.pc+3)≤budget:=(natBits_mono (by omega : before.pc+3≤origin+37)).trans counter
  have lowerPC : natBits ((origin+3)+31)≤budget:=(natBits_mono (by omega : (origin+3)+31≤origin+37)).trans counter
  have lowerReturn : natBits (origin+34)≤budget:=(natBits_mono (by omega : origin+34≤origin+37)).trans counter
  have guardPC : natBits ((origin+34)+3)≤budget:=counter
  have literal:=fetch
  rw [lowerPhaseCode] at literal
  have tagFetch : FetchesCode program before.pc (outputSlotCode 13) := by rw [position];exact literal.append_left.append_left
  obtain ⟨tagTrace,tagHead,tagLast,tagChain,_,tagResources⟩:=
    outputSlot_trace_resources program input before 13 budget (.natural tag) tagStored safe tagBits tagPC tagFetch
  have lowerFetch : FetchesCode program (origin+3) (solveCode (origin+3) false (origin+34)) := by
    simpa only [outputSlot_length] using literal.append_left.append_right
  have taggedAt : tagged.pc=origin+3 := by change before.pc+3=origin+3;rw [position]
  obtain ⟨lower,solved,lowerHead,lowerLast,lowerChain,solvedPC,solvedHeap,solvedLive,lowerSafe⟩:=
    solve_trace_bits program input (origin+3) (origin+34) tagged n k M cap budget false solution taggedAt dimensions payload
      (tagResources tagged (List.mem_of_getLast? tagLast)).2 endBound capBits lowerPC lowerReturn lowerFetch
  have guardFetch : FetchesCode program (origin+34) (stateGuardCode ((origin+34)+3) returnPC) := by
    simpa only [List.length_append,outputSlot_length,solve_length] using literal.append_right
  have tagStill : HeapList solved 13 [.natural tag]:=heapList_same tagStored solvedHeap solvedLive
  obtain ⟨guarded,after,guardHead,guardLast,guardChain,_,afterPC,afterHeap,afterLive,guardResources⟩:=
    guard_trace_resources program input (origin+34) returnPC budget solved tag solvedPC tagStill
      (lowerSafe solved (List.mem_of_getLast? lowerLast)) tagBits guardPC returnBits guardFetch
  have first:=joinTrace_spec program input tagTrace lower before tagged solved (time program tagTrace) (time program lower)
    tagHead tagLast lowerHead lowerLast tagChain lowerChain (le_refl _) (le_refl _)
  have joined:=joinTrace_spec program input (joinTrace tagTrace lower) guarded before solved after
    (time program (joinTrace tagTrace lower)) (time program guarded)
    first.1 first.2.1 guardHead guardLast first.2.2.1 guardChain (le_refl _) (le_refl _)
  have allSafe:=PDCompute.Pack.joinTrace_invariant (joinTrace tagTrace lower) guarded (fun state=>RootD27.Bits.SafeBits state budget)
    (PDCompute.Pack.joinTrace_invariant tagTrace lower (fun state=>RootD27.Bits.SafeBits state budget)
      (fun state member=>(tagResources state member).2) lowerSafe)
    (fun state member=>(guardResources state member).2.2.2)
  exact ⟨joinTrace (joinTrace tagTrace lower) guarded,after,joined.1,joined.2.1,joined.2.2.1,afterPC,
    afterHeap.trans solvedHeap,afterLive.trans solvedLive,allSafe⟩

/-- Complete exact/bracket68-op numerical execution, with arbitrary
dirty caller carry at ONE B and actual original physical table ends. -/
theorem state_trace_bits (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (before : State) (n k M cap budget : ℕ) (state : MultiplierState)
    (position : before.pc=origin) (dimensions : PreparedDimensions before n k M)
    (payload : StatePayload before n k M state) (safe : RootD27.Bits.SafeBits before budget)
    (ends : StateEndBound n k M cap state) (capBits : 1+natBits cap≤budget)
    (counter : natBits (origin+68)≤budget) (returnBits : natBits returnPC≤budget)
    (fetch : FetchesCode program origin (stateCode origin returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ after.pc=returnPC ∧
      after.heap=before.heap ∧ after.live=before.live ∧ ∀ current∈trace,RootD27.Bits.SafeBits current budget := by
  have lowerCounter : natBits (origin+37)≤budget:=(natBits_mono (by omega : origin+37≤origin+68)).trans counter
  have upperCounter : natBits ((origin+37)+31)≤budget:=counter
  have literal:=fetch
  rw [stateCode_decompose] at literal
  cases state with
  | exact solution =>
    obtain ⟨trace,after,head,last,chain,pc,heap,live,bounded⟩:=
      lowerPhase_trace_bits program input origin returnPC before n k M 0 cap budget solution position dimensions payload.1 payload.2
        safe ends capBits lowerCounter returnBits literal.append_left
    exact ⟨trace,after,head,last,chain,pc,heap,live,bounded⟩
  | bracket lower upper =>
    obtain ⟨first,middle,firstHead,firstLast,firstChain,middlePC,middleHeap,middleLive,firstSafe⟩:=
      lowerPhase_trace_bits program input origin returnPC before n k M 1 cap budget lower position dimensions payload.1 payload.2.1
        safe ends.1 capBits lowerCounter returnBits literal.append_left
    have atUpper : middle.pc=origin+37 := by simpa using middlePC
    have upperDimensions:=dimensions.preserve middleHeap middleLive
    have upperPayload:=payload.2.2.preserve middleHeap middleLive
    have upperFetch : FetchesCode program (origin+37) (solveCode (origin+37) true returnPC) := by
      simpa only [lowerPhase_length] using literal.append_right
    obtain ⟨second,after,secondHead,secondLast,secondChain,afterPC,afterHeap,afterLive,secondSafe⟩:=
      solve_trace_bits program input (origin+37) returnPC middle n k M cap budget true upper atUpper upperDimensions upperPayload
        (firstSafe middle (List.mem_of_getLast? firstLast)) ends.2 capBits upperCounter returnBits upperFetch
    have joined:=joinTrace_spec program input first second before middle after (time program first) (time program second)
      firstHead firstLast secondHead secondLast firstChain secondChain (le_refl _) (le_refl _)
    exact ⟨joinTrace first second,after,joined.1,joined.2.1,joined.2.2.1,afterPC,afterHeap.trans middleHeap,afterLive.trans middleLive,
      PDCompute.Pack.joinTrace_invariant first second (fun current=>RootD27.Bits.SafeBits current budget) firstSafe secondSafe⟩

/-- ONE SAME actual caller trace has original function/time/physical
resources AND every-prefix SAMEB. First-exit identity is proved, never
assumed. The return geometry is a fixed code-layout fact, not inputdata. -/
theorem state_trace_resources (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (before : State) (n k M cap budget : ℕ) (state : MultiplierState)
    (position : before.pc=origin) (dimensions : PreparedDimensions before n k M)
    (payload : StatePayload before n k M state) (safe : RootD27.Bits.SafeBits before budget)
    (ends : StateEndBound n k M cap state) (capBits : 1+natBits cap≤budget)
    (counter : natBits (origin+68)≤budget) (returnBits : natBits returnPC≤budget)
    (returnOutside : returnPC<origin ∨ origin+68≤returnPC)
    (fetch : FetchesCode program origin (stateCode origin returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤1024*((encodeState state).length+1) ∧ after.pc=returnPC ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output++encodeState state ∧
      (∀ current∈trace,RootD27.Core.EmittedPrefix before (encodeState state) current) ∧
      peakCells trace≤workingCells before+(encodeState state).length ∧
      (∀ current∈trace.dropLast,origin≤current.pc ∧ current.pc<origin+68) ∧
      peakOperandBits trace≤budget ∧ ∀ current∈trace,RootD27.Bits.SafeBits current budget := by
  obtain ⟨functional,after,head,last,chain,cost,pc,heap,live,output,prefixes,space,scope⟩:=
    state_trace_in_program program input origin returnPC before n k M state position dimensions payload fetch
  obtain ⟨numeric,numericAfter,numericHead,numericLast,numericChain,numericPC,_,_,numericSafe⟩:=
    state_trace_bits (locatedProgram origin returnPC) input origin returnPC before n k M cap budget state position dimensions payload
      safe ends capBits counter returnBits (located_fetch origin returnPC)
  have numericScope : ∀ current∈numeric.dropLast,origin≤current.pc ∧ current.pc<origin+68 := by
    simpa only [List.size_toArray,state_length] using
      PDLower.CalibrationCompute.located_chain_scope origin (stateCode origin returnPC).toArray input numeric numericChain
  have fetched : ∀ current∈numeric.dropLast,(locatedProgram origin returnPC)[current.pc]?=program[current.pc]? := by
    intro current member
    have bounds:=numericScope current member
    have addressed : origin+(current.pc-origin)=current.pc:=Nat.add_sub_of_le bounds.1
    have offsetBound : current.pc-origin<(stateCode origin returnPC).length := by rw [state_length];omega
    calc
      (locatedProgram origin returnPC)[current.pc]?=(locatedProgram origin returnPC)[origin+(current.pc-origin)]? := by rw [addressed]
      _=(stateCode origin returnPC)[current.pc-origin]? := by rw [locatedProgram,locatedBlock_fetch,List.getElem?_toArray]
      _=program[origin+(current.pc-origin)]? := (fetch (current.pc-origin) offsetBound).symm
      _=program[current.pc]? := by rw [addressed]
  have callerChain:=RootD27.Core.chain_same_input_of_fetch _ program input numeric fetched numericChain
  have functionalProper : ∀ current∈functional.dropLast,¬current.pc=returnPC := by
    intro current member equal
    have bounds:=scope current member
    rcases returnOutside with lower|upper <;> omega
  have numericProper : ∀ current∈numeric.dropLast,¬current.pc=returnPC := by
    intro current member equal
    have bounds:=numericScope current member
    rcases returnOutside with lower|upper <;> omega
  have same:=ROOT.ActualTrace.firstExit_unique_of_endpoints (fun current=>step program input current)
    (fun current=>current.pc=returnPC) before after numericAfter functional numeric
    head numericHead chain callerChain last numericLast pc numericPC functionalProper numericProper
  have allSafe : ∀ current∈functional,RootD27.Bits.SafeBits current budget := by rw [same.1];exact numericSafe
  exact ⟨functional,after,head,last,chain,cost,pc,heap,live,output,prefixes,space,scope,
    PDCompute.Pack.safeBits_peak functional budget allSafe,allSafe⟩

end PDCompute.CoreEmit

