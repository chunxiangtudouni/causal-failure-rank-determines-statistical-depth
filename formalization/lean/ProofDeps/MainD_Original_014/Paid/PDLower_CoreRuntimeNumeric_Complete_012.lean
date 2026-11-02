module

public import Paid.PDLower_CoreRuntimeNumeric_SolverStub_005
public import Paid.PDLower_CoreRuntimeNumeric_CopySaved_011
public import Paid.PDCompute_SolverReturnMarker_220
public import Paid.PDCompute_CoreSearchLoop_SingleEntry_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDROC.DataBits
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open RootD27.Core RootD27.Bits PDCompute.CoreSearchLoop PDCompute.NatControl

namespace PDLower.CoreRuntimeNumeric

/-- Original cache geometry, for any actual solver/statistics prefix.
The precise fixed cache survives without cleaning the old live world. -/
theorem original_cache_of_runtime_region (P : Parameters) (before after : State) (target : ℕ)
    (upper : target+2<46)
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (memory : RegionMemory before after
      (workspace (99+2*P.certificate.M) P.certificate.stages P.tools∪{target,target+1,target+2})) :
    HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
  apply memory.heapList stored
  intro offset inside member
  rcases Finset.mem_union.mp member with work|metadata
  · exact original_endpoint_avoids_solver P P.certificate.stages P.tools offset inside work
  · simp only [Finset.mem_insert,Finset.mem_singleton] at metadata
    omega

/-- SAME actual trace bounds imply the original full peakOperandBits. -/
theorem safe_trace_peak (trace : List State) (budget : ℕ)
    (safe : ∀ state∈trace,SafeBits state budget) : peakOperandBits trace≤budget :=
  PDCompute.Pack.safeBits_peak trace budget safe

/-- The exact indexed windows survive actual concatenation; the local
window equality is supplied by the frozen CallAt padding interfaces. -/
theorem refinement_append (program : Program) (labels : RoutineLabels) (P : Parameters) (fee : ℚ)
    (constant : ℕ) (first later : List State)
    (firstCalls : SolverCallRefinement program labels P fee constant first)
    (laterCalls : SolverCallRefinement program labels P fee constant later) :
    SolverCallRefinement program labels P fee constant (first++later) := by
  intro index state found position
  change CallAt program labels P fee constant (first++later) index state
  by_cases left : index<first.length
  · have earlier : first[index]?=some state := by
      rwa [List.getElem?_append_left left] at found
    have window : CallAt program labels P fee constant first index state := firstCalls index state earlier position
    exact window.append_right later
  · have right : first.length≤ index := by omega
    have laterFound : later[index-first.length]?=some state := by
      rwa [List.getElem?_append_right right] at found
    have window : CallAt program labels P fee constant later (index-first.length) state :=
      laterCalls _ state laterFound position
    have shifted := window.prepend first
    have location : first.length+(index-first.length)=index := by omega
    simpa only [location] using shifted

/-- An actual final epilogue marker supplies the ORIGINAL index-zero
call obligation. Cutting the final real jump state only decreases time. -/
theorem callAt_zero_of_marker (program : Program) (labels : RoutineLabels)
    (P : Parameters) (fee penalty : ℚ) (constant : ℕ) (input : List Cell) (trace : List State)
    (before after : State) (markerPC address : ℕ)
    (head : trace.head?=some before) (position : before.pc=labels.solveEntry)
    (total : before.register .total=.rational penalty)
    (marked : ReturnMarker program input trace after markerPC)
    (markerAbove : labels.solveEntry<markerPC) (label : markerPC=labels.solveReturn)
    (pointer : after.register .address=.natural address)
    (table : HeapList after address
      (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)))
    (cost : time program trace≤constant*(P.certificate.stages+1)*(P.tools+1)*(P.certificate.M+1)) :
    CallAt program labels P fee constant trace 0 before := by
  obtain ⟨front,marker,shape,pc,register,heap,live,_output,_jump⟩ := marked
  have order : 0<front.length := by
    by_contra notPositive
    have empty : front=[] := List.length_eq_zero_iff.mp (by omega)
    have markerHead : trace.head?=some marker := by rw [shape,empty];rfl
    have same : marker=before := Option.some.inj (markerHead.symm.trans head)
    have counters := congrArg State.pc same
    omega
  have found : (trace)[front.length]?=some marker := by
    rw [shape,List.getElem?_append_right (le_refl _),Nat.sub_self]
    rfl
  have markerTable : HeapList marker address
      (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)) := by
    simpa only [HeapList,heapSegment,heap,live] using table
  have split : trace=(front++[marker])++[after] := by rw [shape,List.append_assoc];rfl
  have cut : trace.take (front.length+1)=front++[marker] := by
    rw [split]
    exact List.take_left' (by simp)
  have cutCost : time program (front++[marker])≤time program trace := by
    rw [split]
    simp only [time_append]
    omega
  refine ⟨penalty,by rw [total];rfl,front.length,marker,address,order,found,pc.trans label,?_,markerTable.1,markerTable.2,?_⟩
  · rw [register,pointer]
    rfl
  · simp only [Nat.sub_zero,List.drop_zero,cut]
    exact cutCost.trans cost

/-- The fixed physical last opcode of the original shared solver. -/
def commonSolverMarkerPC (labels : RoutineLabels) : ℕ :=
  (labels.solveEntry+1)+46+(matrixCode .liveHeap (labels.solveEntry+1+46)).length+232

/-- Transfer the new callee marker to an ALREADY constructed resource
trace only after proving both traces' genuine first return identity.
The actual caller return is below the callee and differs from the fixed
common marker. No function, memory, bits or time witness is replaced. -/
theorem stub_trace_calls (P : Parameters) (fee penalty : ℚ) (program : Program) (input : List Cell)
    (labels : RoutineLabels) (before after : State) (trace : List State) (returnPC budget : ℕ)
    (position : before.pc=labels.solveEntry) (returnBelow : returnPC<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1)))
    (fresh : before.register .fresh=.natural (99+2*P.certificate.M))
    (old : before.register .old=.natural returnPC) (address : before.register .address=.natural 96)
    (total : before.register .total=.rational penalty)
    (index : before.register .index=.natural P.certificate.stages)
    (value : before.register .value=.natural P.tools) (flag : before.register .flag=.rational fee)
    (endpoint : EndpointSource .liveHeap input P 96 before)
    (safe : SafeBits before budget) (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (controlRoom : runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (scalarRoom : 4194304*solverBitScale P fee penalty P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=commonSolverMarkerPC labels)
    (head : trace.head?=some before) (last : trace.getLast?=some after)
    (chain : trace.IsChain (fun first later=>step program input first=some later))
    (cost : time program trace≤38100*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools)
    (returned : Return P fee penalty P.certificate.stages P.tools (99+2*P.certificate.M) returnPC before after)
    (count : PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1)
    (scope : ∀ state∈trace.dropLast,labels.solveEntry≤state.pc) :
    ReturnMarker program input trace after (commonSolverMarkerPC labels) ∧
      SolverCallRefinement program labels P fee 40000 trace := by
  let began : State := {before with pc:=labels.solveEntry+1}
  have context := runtime_control_context P (labels.solveEntry+1) budget controlRoom
  have beganSafe : SafeBits began budget := safe.withPC _ (context.pc _ (by omega))
  have indexBits : 1+natBits (P.certificate.M+1)≤budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : P.certificate.M+1≤99+2*P.certificate.M)) 1).trans baseBits
  have sourceBits : 1+natBits (96+(1+2*(P.certificate.M+1)))≤budget := by
    have same : 96+(1+2*(P.certificate.M+1))=99+2*P.certificate.M := by omega
    rw [same]
    exact baseBits
  obtain ⟨body,computed,bh,bl,bc,bt,bodyReturn,_memory,_space,_peak,_bits,bodyScope,_dense,_root,marked⟩ :=
    solver_callee_given_budget_marker_in_program .liveHeap program input (labels.solveEntry+1) bodyFetch P fee penalty began
      (99+2*P.certificate.M) P.certificate.stages P.tools 96 returnPC rfl fresh old address total index value flag endpoint
      (original_endpoint_avoids_solver P P.certificate.stages P.tools)
      _ _ budget context beganSafe scalarRoom indexBits sourceBits
  have jump : step program input before=some began := by simp only [step,position,stubFetch];rfl
  have firstChain : [before,began].IsChain (fun first later=>step program input first=some later) :=
    List.isChain_cons_cons.mpr ⟨jump,.singleton began⟩
  have joined := joinTrace_spec program input [before,began] body before began computed 30
    (38000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools+15)
    rfl rfl bh bl firstChain bc (time_le_length program [before,began]) bt
  have bodyNonempty : body≠[] := by intro empty;simp [empty] at bh
  have canonicalProper : ∀ state∈(joinTrace [before,began] body).dropLast,¬state.pc=returnPC := by
    intro state member same
    change state∈([before]++body).dropLast at member
    rw [List.dropLast_append_of_ne_nil bodyNonempty] at member
    rcases List.mem_append.mp member with entryMember|bodyMember
    · have equal := List.mem_singleton.mp entryMember
      subst state
      omega
    · have low := (bodyScope state bodyMember).1
      omega
  have actualProper : ∀ state∈trace.dropLast,¬state.pc=returnPC := by
    intro state member same
    have low := scope state member
    omega
  have canonicalMarker : ReturnMarker program input (joinTrace [before,began] body) computed (commonSolverMarkerPC labels) :=
    marked.join_left [before,began]
  have actualMarker : ReturnMarker program input trace after (commonSolverMarkerPC labels) :=
    canonicalMarker.identify joined.1 head joined.2.2.1 chain joined.2.1 last bodyReturn.1 returned.1 canonicalProper actualProper
  obtain ⟨_pc,_fresh,_old,pointer,_index,table,_output,_frame⟩ := returned
  have fullCost : time program trace≤40000*(P.certificate.stages+1)*(P.tools+1)*(P.certificate.M+1) := by
    calc
      _≤38100*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools := cost
      _≤40000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 38100≤40000))
      _=40000*(P.certificate.stages+1)*(P.tools+1)*(P.certificate.M+1) := by
        unfold PDCompute.Solver.entryCount
        ring
  have markerAbove : labels.solveEntry<commonSolverMarkerPC labels := by unfold commonSolverMarkerPC;omega
  have window := callAt_zero_of_marker program labels P fee penalty 40000 input trace before after
    (commonSolverMarkerPC labels) (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
    head position total actualMarker markerAbove markerLabel.symm pointer table fullCost
  exact ⟨actualMarker,refinement_of_entry_window program labels P fee 40000 trace before head position count window⟩

end PDLower.CoreRuntimeNumeric
