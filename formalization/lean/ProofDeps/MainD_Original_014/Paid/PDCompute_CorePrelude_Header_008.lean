module
public import Paid.PDCompute_CorePrelude_Calibration_007
public import Paid.RootD27Core_HeaderCode_045

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section

namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDCompute.Solver PDMenu.ComputeFrame RootD27.Core RootD27.Bits

/-- Original fresh13/header37/fresh0, with all actual dirty old workspace
and prior output carried. A real local trace proves first arrival782;
only successful fetched instructions are transferred into the caller. -/
theorem header_resources (P : Parameters) (fee : ℚ) (program : Program) (input : List Cell)
    (before : State) (position : before.pc=afterCalibration)
    (prepared : HeapList before 0 (preparedInput P fee))
    (cache : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (safe : SafeBits before (calibrationBudget P fee))
    (fetch : FetchesCode program afterCalibration (PDCompute.CorePrelude.headerCode afterCalibration)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤2535 ∧ after.pc=bodyStart ∧
      PDCompute.CoreSearchLoop.Ready P fee after ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+48 ∧
      (∀ state∈trace,RegionMemory before state (cellRegion 13 48)) ∧
      (∀ state∈trace,SafeBits state (prefixBudget P fee)) ∧
      (∀ state∈trace,afterCalibration≤state.pc ∧ state.pc≤bodyStart) ∧
      (∀ state∈trace.dropLast,state.pc<bodyStart) := by
  let code:=PDCompute.CorePrelude.headerCode afterCalibration
  let localProgram:=locatedBlock afterCalibration code.toArray
  have localFetch : FetchesCode localProgram before.pc (coreHeaderCode before.pc):=by
    rw [position]
    have same : coreHeaderCode afterCalibration=code:=by
      simp only [coreHeaderCode,code,PDCompute.CorePrelude.headerCode,solverHeaderCode,List.append_assoc,Nat.add_assoc]
    rw [same]
    intro offset inside
    rw [locatedBlock_fetch,List.getElem?_toArray]
  obtain ⟨trace,after,head,last,chain,cost,header,preparedAfter,fresh,afterPC,output,peak,resources⟩:=
    core_header_initialize_code_actual P fee input localProgram before prepared localFetch
  have firstEnd : after.pc=bodyStart:=by unfold bodyStart;omega
  have moved:=located_trace_in_program program input afterCalibration code trace fetch chain
  have bounded : coreHeaderBudget before≤prefixBudget P fee:=by
    have initialBound : PDCompute.Pack.initialBits before≤calibrationBudget P fee:=by
      apply PDCompute.Pack.safeBits_peak
      intro state member
      have same:=List.mem_singleton.mp member
      subst state
      exact safe
    have room:=(prefix_certificate_bounds P fee).2.2
    unfold coreHeaderBudget
    have pc : before.pc+39=bodyStart:=by unfold bodyStart;omega
    rw [pc]
    omega
  have finalMemory:=(resources after (List.mem_of_getLast? last)).1
  have cacheAfter : HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList):=by
    apply finalMemory.heapList cache
    intro offset inside
    rw [mem_cellRegion_iff]
    omega
  refine ⟨trace,after,head,last,moved.1,moved.2.1.trans (Nat.add_le_add_right cost 15),firstEnd,
    ⟨header,fresh,preparedAfter,cacheAfter⟩,output,peak,
    fun state member=>(resources state member).1,
    fun state member=>PDCompute.Pack.safeBits_mono (resources state member).2.1 bounded,?_,?_⟩
  · intro state member
    have range:=(resources state member).2.2
    rw [position] at range
    change afterCalibration≤state.pc ∧ state.pc≤afterCalibration+39 at range
    exact range
  · intro state member
    have range:=moved.2.2 state member
    rw [header_length] at range
    exact range.2

end PDCompute.CorePrelude
