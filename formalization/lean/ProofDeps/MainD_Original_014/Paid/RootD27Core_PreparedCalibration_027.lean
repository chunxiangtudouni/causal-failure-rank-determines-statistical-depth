module

public import Paid.RootD27Core_HeapEndpointSpace_026
public import Paid.RootD27Core_CalibrationHeapCall_025
public import Paid.RootD27Core_PreparedHeapEndpoint_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

def preparedCalibrationReturnPC : ℕ := 316+(PDLower.CalibrationCompute.kernel 316).size

/-- A single fixed original prepared-ROM prefix before all P/fee inputs:
real copy13, complete endpoint computation/output, real heap calibration
arguments and complete emitting calibration, followed by caller code. -/
def preparedCalibrationProgram (continuation : Program) : Program :=
  calibrationCallerProgram (preparedHeapEndpointProgram []) continuation preparedCalibrationReturnPC

theorem preparedEndpointLeading_size : (preparedHeapEndpointProgram []).size=302 := by
  simp only [preparedHeapEndpointProgram,List.size_toArray,List.length_append,inputCopy_length,
    endpointHeapOutput_length,List.length_nil]

theorem preparedCalibration_toList (continuation : Program) :
    (preparedCalibrationProgram continuation).toList=
      inputCopyCode 13++(endpointHeapOutputCode 39 48 96 302++
        (calibrationHeapArgumentsCode preparedCalibrationReturnPC++
          ((PDLower.CalibrationCompute.kernel 316).toList++continuation.toList))) := by
  unfold preparedCalibrationProgram calibrationCallerProgram
  rw [calibrationCallerPrefix_size,preparedEndpointLeading_size]
  simp only [calibrationCallerPrefix,preparedHeapEndpointProgram,Array.toList_append,
    List.append_nil,List.append_assoc]

theorem original_prepared_endpoint_calibration_prefix (continuation : Program)
    (P : Parameters) (fee : ℚ) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some initial ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step (preparedCalibrationProgram continuation) (preparedInput P fee) first=some later) ∧
      time (preparedCalibrationProgram continuation) trace≤
        8500*(P.certificate.M+1)+30300*(P.certificate.Q+1)*(P.certificate.M+1)^2 ∧
      after.pc=preparedCalibrationReturnPC ∧ HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      PDLower.CalibrationCompute.HeapList after
        (PDLower.CalibrationCompute.resultBase (99+2*P.certificate.M) P.certificate.M)
        (encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList) ∧
      after.output=encodeList encodeEndpoint P.endpointCache.toList++
        encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList ∧
      peakCells trace≤102*(P.certificate.M+1) ∧
      (∀ state∈trace,workingCells state≤102*(P.certificate.M+1)) := by
  let program:=preparedCalibrationProgram continuation
  have literal : FetchesCode program 0 (program.toList) := by
    intro offset _inside
    simp only [Nat.zero_add,Array.getElem?_toList]
  rw [preparedCalibration_toList] at literal
  have copyFetch : FetchesCode program initial.pc (inputCopyCode 13):=literal.append_left
  obtain ⟨copied,ch,cl,cc,ct,copyMemory⟩:=inputCopy_actual program (preparedInput P fee) initial 13
    (by change 13≤13;decide) copyFetch
  let middle:=inputCopyResult (preparedInput P fee) initial 13
  have middlePC : middle.pc=39 := by rw [inputCopy_pc];rfl
  have copyBound (state : State) (member : state∈copied) : workingCells state≤20 := by
    have bound:=inputCopy_workingCells initial state 13 (copyMemory state member)
    exact bound
  have middleBound:=copyBound middle (List.mem_of_getLast? cl)
  have prepared : HeapList middle 0 (preparedInput P fee) := by
    have full : (preparedInput P fee).take 13=preparedInput P fee := by
      apply List.take_of_length_le
      change 13≤13
      decide
    simpa only [full] using inputCopy_heapList (preparedInput P fee) initial 13
  have endpointFetch : FetchesCode program middle.pc (endpointHeapOutputCode middle.pc 48 96 302) := by
    rw [middlePC]
    simpa only [inputCopy_length,Nat.zero_add,show 3*13=39 from rfl] using literal.append_right.append_left
  obtain ⟨endpoints,computed,eh,el,ec,et,endpointPC,cache,retained,endpointOutput,_endpointPeak,endpointBounds⟩:=
    endpoint_heap_output_actual_space P fee (preparedInput P fee) program middle 48 96 302
      prepared (by decide) (by decide) endpointFetch
  have computedBound : workingCells computed≤4*P.certificate.M+74 := by
    have bound:=endpointBounds computed (List.mem_of_getLast? el)
    omega
  have computedOutput : computed.output=encodeList encodeEndpoint P.endpointCache.toList := by
    have empty : middle.output=[]:=inputCopy_output (preparedInput P fee) initial 13
    simpa only [empty,List.nil_append] using endpointOutput
  have firstJoin:=joinTrace_spec program (preparedInput P fee) copied endpoints initial middle computed
    795 (7700*(P.certificate.M+1)) ch cl eh el cc ec ct et
  have callPosition : computed.pc=(preparedHeapEndpointProgram []).size := by
    rw [preparedEndpointLeading_size]
    exact endpointPC
  obtain ⟨calibration,after,ah,al,ac,calibrationTime,returned,finalPrepared,finalEndpoints,calibrationPeak⟩:=
    calibration_from_prepared_heap_actual P fee (preparedHeapEndpointProgram []) continuation
      preparedCalibrationReturnPC (preparedInput P fee) computed callPosition retained cache
  have joined:=joinTrace_spec program (preparedInput P fee) (joinTrace copied endpoints) calibration
    initial computed after (8500*(P.certificate.M+1))
      (30300*(P.certificate.Q+1)*(P.certificate.M+1)^2)
      firstJoin.1 firstJoin.2.1 ah al firstJoin.2.2.1 ac
      (firstJoin.2.2.2.trans (prepared_heap_endpoint_budget P.certificate.M)) calibrationTime
  have allBounds : ∀ state∈joinTrace (joinTrace copied endpoints) calibration,
      workingCells state≤102*(P.certificate.M+1) := by
    intro state member
    rcases joinTrace_member member with earlier|later
    · rcases joinTrace_member earlier with copyMember|endpointMember
      · have bound:=copyBound state copyMember
        omega
      · have bound:=endpointBounds state endpointMember
        omega
    · have bound:=(workingCells_le_peak_of_member calibration state later).trans calibrationPeak
      rw [PDLower.CalibrationCompute.workspaceSize_linear] at bound
      change workingCells state≤workingCells computed+(6*P.certificate.M+25)+(2*P.certificate.M+3) at bound
      omega
  exact ⟨joinTrace (joinTrace copied endpoints) calibration,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2,returned.1,finalPrepared,finalEndpoints,returned.2.2.2.2.2.1,
    by simpa only [computedOutput] using returned.2.2.2.2.2.2.1,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allBounds,allBounds⟩

end RootD27.Core
