module

public import Paid.RootD27Core_CalibrationCaller_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (HeapList CallArguments Return workspaceSize rowWidth kernel labelAddress)

/-- Only static caller code and return addresses occur in the program.
The actual M/Q/gamma and variable workspace address are loaded/computed
from the original prepared heap, rather than installed in the program. -/
def calibrationCallerPrefix (leading : Program) (returnPC : ℕ) : Program :=
  leading++(calibrationHeapArgumentsCode returnPC).toArray

def calibrationCallerProgram (leading suffix : Program) (returnPC : ℕ) : Program :=
  calibrationCallerPrefix leading returnPC++kernel (calibrationCallerPrefix leading returnPC).size++suffix

theorem calibrationCallerPrefix_size (leading : Program) (returnPC : ℕ) :
    (calibrationCallerPrefix leading returnPC).size=leading.size+14 := by
  simp only [calibrationCallerPrefix,Array.size_append,List.size_toArray,calibrationHeapArguments_length]

theorem calibrationCaller_arguments_fetch (leading suffix : Program) (returnPC : ℕ) :
    FetchesCode (calibrationCallerProgram leading suffix returnPC) leading.size
      (calibrationHeapArgumentsCode returnPC) := by
  intro offset inside
  have prefixBound : leading.size+offset<(calibrationCallerPrefix leading returnPC).size := by
    rw [calibrationCallerPrefix_size]
    rw [calibrationHeapArguments_length] at inside
    omega
  unfold calibrationCallerProgram
  rw [Array.getElem?_append_left (by simp only [Array.size_append];omega)]
  rw [Array.getElem?_append_left prefixBound]
  unfold calibrationCallerPrefix
  rw [Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,List.getElem?_toArray]

/-- Real original heap arguments followed by the actual complete emitting
calibration kernel and its genuine indirect return. All old scratch/live
cells and output remain present. Time and peak space use this ONE trace. -/
theorem calibration_from_prepared_heap_actual (P : Parameters) (fee : ℚ)
    (leading suffix : Program) (returnPC : ℕ) (input : List Cell) (before : State)
    (position : before.pc=leading.size)
    (prepared : HeapList before 0 (preparedInput P fee))
    (endpointHeap : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step (calibrationCallerProgram leading suffix returnPC) input first=some later) ∧
      time (calibrationCallerProgram leading suffix returnPC) trace≤
        30300*(P.certificate.Q+1)*(P.certificate.M+1)^2 ∧
      Return P (99+2*P.certificate.M) returnPC before after ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      peakCells trace≤workingCells before+workspaceSize P.certificate.M+rowWidth P.certificate.M := by
  let program:=calibrationCallerProgram leading suffix returnPC
  let middle:=calibrationHeapArgumentsResult P before returnPC
  have fetched : FetchesCode program before.pc (calibrationHeapArgumentsCode returnPC) := by
    rw [position]
    exact calibrationCaller_arguments_fetch leading suffix returnPC
  obtain ⟨setupTrace,sh,sl,sc,st,sm⟩:=
    calibrationHeapArguments_actual P fee input program before returnPC prepared fetched
  have middleCache : HeapList middle 96 (encodeList encodeEndpoint P.endpointCache.toList) := endpointHeap
  have middlePC : middle.pc=labelAddress (calibrationCallerPrefix leading returnPC).size .enter := by
    rw [PDLower.CalibrationCompute.entry_address,calibrationCallerPrefix_size]
    change before.pc+14=leading.size+14
    rw [position]
  obtain ⟨body,after,bh,bl,bc,bt,returned,peak⟩:=
    calibration_callee_in_caller P (calibrationCallerPrefix leading returnPC) suffix input
      (99+2*P.certificate.M) 96 returnPC middle
      (calibrationHeapArguments_callArguments P before returnPC) middleCache
      (original_endpoint_avoids_calibration P) middlePC
  have joined:=joinTrace_spec program input setupTrace body before middle after
    225 (30000*(P.certificate.Q+1)*(P.certificate.M+1)^2+15) sh sl bh bl sc bc st bt
  change Return P (99+2*P.certificate.M) returnPC before after at returned
  have frame : MemoryFrame (PDLower.CalibrationCompute.workspace (99+2*P.certificate.M) P.certificate.M) before after :=
    returned.2.2.2.2.2.2.2
  refine ⟨joinTrace setupTrace body,after,joined.1,joined.2.1,joined.2.2.1,?_,returned,?_,?_,?_⟩
  · have positive : 0<(P.certificate.Q+1)*(P.certificate.M+1)^2:=by positivity
    have budget : 225+(30000*(P.certificate.Q+1)*(P.certificate.M+1)^2+15)≤
        30300*(P.certificate.Q+1)*(P.certificate.M+1)^2 := by
      simp only [Nat.mul_assoc]
      omega
    exact joined.2.2.2.trans budget
  · apply PDLower.CalibrationCompute.HeapList.memoryFrame prepared _ frame
    intro offset inside
    change offset<13 at inside
    exact original_prepared_avoids_calibration P offset inside
  · exact PDLower.CalibrationCompute.HeapList.memoryFrame endpointHeap _ frame (original_endpoint_avoids_calibration P)
  · apply PDLower.CalibrationCompute.peakCells_le_of_forall
    intro state member
    rcases joinTrace_member member with setupMember|bodyMember
    · obtain ⟨_heap,live,output⟩:=sm state setupMember
      simp only [workingCells,live,output]
      omega
    · have bound:=(workingCells_le_peak_of_member body state bodyMember).trans peak
      exact bound

end RootD27.Core
