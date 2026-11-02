module

public import Paid.RootD27Core_CalibrationHeapArguments_023
public import Paid.PDLower_CalibrationCompute_CalleeRecords_083
public import Paid.RootD27Core_EmitLoop_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (HeapList CallArguments Return workspaceSize rowWidth kernel labelAddress)

theorem calibrationHeapArguments_callArguments (P : Parameters) (before : State) (returnPC : ℕ) :
    CallArguments P (99+2*P.certificate.M) 96 returnPC
      (calibrationHeapArgumentsResult P before returnPC) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem original_endpoint_avoids_calibration (P : Parameters) (offset : ℕ)
    (inside : offset<(encodeList encodeEndpoint P.endpointCache.toList).length) :
    96+offset∉PDLower.CalibrationCompute.workspace (99+2*P.certificate.M) P.certificate.M := by
  rw [PDLower.CalibrationCompute.encodeEndpointCache_length] at inside
  change offset<2*P.certificate.M+3 at inside
  intro member
  obtain ⟨index,_,equal⟩:=Finset.mem_image.mp member
  omega

theorem original_prepared_avoids_calibration (P : Parameters) (offset : ℕ)
    (inside : offset<13) :
    0+offset∉PDLower.CalibrationCompute.workspace (99+2*P.certificate.M) P.certificate.M := by
  intro member
  obtain ⟨index,_,equal⟩:=Finset.mem_image.mp member
  omega

/-- Preserve the actual callee's ONE witness when embedding in real caller
code. In particular the original return/output/peak-record theorem refers
to exactly the trace executed by this caller and its unchanged input. -/
theorem calibration_callee_in_caller (P : Parameters) (beforeCode suffix : Program)
    (input : List Cell) (base endpoints returnPC : ℕ) (before : State)
    (arguments : CallArguments P base endpoints returnPC before)
    (endpointHeap : HeapList before endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (separate : ∀ offset<(encodeList encodeEndpoint P.endpointCache.toList).length,
      endpoints+offset∉PDLower.CalibrationCompute.workspace base P.certificate.M)
    (position : before.pc=labelAddress beforeCode.size .enter) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>
        step (beforeCode++kernel beforeCode.size++suffix) input first=some later) ∧
      time (beforeCode++kernel beforeCode.size++suffix) trace≤
        30000*(P.certificate.Q+1)*(P.certificate.M+1)^2+15 ∧
      Return P base returnPC before after ∧
      peakCells trace≤workingCells before+workspaceSize P.certificate.M+rowWidth P.certificate.M := by
  obtain ⟨trace,after,head,last,chain,cost,returned,peak⟩:=
    PDLower.CalibrationCompute.callee_with_records P beforeCode.size base endpoints returnPC input before
      arguments endpointHeap separate position
  have embedded:=PDLower.CalibrationCompute.kernel_chain_in_caller beforeCode suffix input input trace
    (PDLower.CalibrationCompute.located_chain_scope beforeCode.size (kernel beforeCode.size) input trace chain) chain
  exact ⟨trace,after,head,last,embedded.1,
    embedded.2.trans (Nat.add_le_add_right cost 15),returned,peak⟩

theorem workingCells_le_peak_of_member (trace : List State) (state : State) (member : state∈trace) :
    workingCells state≤peakCells trace := by
  have mapped : workingCells state∈trace.map workingCells:=List.mem_map.mpr ⟨state,member,rfl⟩
  have nonempty : trace.map workingCells≠[] := by
    intro empty
    rw [empty] at mapped
    cases mapped
  unfold peakCells
  rw [List.foldl_max_eq_max nonempty]
  exact (List.le_max_of_mem mapped).trans (le_max_right _ _)

end RootD27.Core
