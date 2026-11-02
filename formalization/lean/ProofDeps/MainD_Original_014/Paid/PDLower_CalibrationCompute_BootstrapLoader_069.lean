module

public import Paid.PDLower_CalibrationCompute_BootstrapStart_060
public import Paid.PDLower_CalibrationCompute_BootstrapLoop_058
public import Paid.PDLower_CalibrationCompute_BootstrapEnd_068

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

/-- A genuine empty-live caller is enough: every input is loaded by the
fixed loader, the complete original endpoint list is copied, and the
workspace's disjointness follows from the actual copy frame. -/
theorem bootstrapLoader (P : Parameters) (before : State)
    (position : before.pc=0) (empty : before.live=∅) :
    ∃ after : State,StandaloneSegment (calibrationInput P) before after (1000*(P.certificate.M+1)) ∧
      after.pc=1 ∧ Entry P (rowWidth P.certificate.M) 0 (mainStart+27) after ∧
      after.output=before.output ∧ after.live=Finset.range (rowWidth P.certificate.M) := by
  let entered : State := {before with pc:=mainStart}
  have jumped : step calibrate (calibrationInput P) before=some entered := by
    simp only [step,position,initial_jump_fetch,Instruction.execute]
    rfl
  have jumpRun := standalone_oneStep (calibrationInput P) before entered jumped
  let started := bootstrapStartResult entered P
  have startRun : StandaloneSegment (calibrationInput P) entered started 195 :=
    bootstrapStart_segment P entered rfl
  let values := encodeList encodeEndpoint P.endpointCache.toList
  have size : values.length=rowWidth P.certificate.M := encodeEndpointCache_length P
  have data (index : ℕ) (inside : index<values.length) :
      (calibrationInput P)[3+([] : List Cell).length+index]?=some values[index] := by
    change ([Cell.natural P.certificate.M,.natural P.certificate.Q,.rational P.certificate.gamma]++values)[3+index]?=some values[index]
    rw [List.getElem?_append_right (by change 3≤3+index; omega)]
    simpa only [List.length_cons,List.length_nil,Nat.add_sub_cancel_left] using
      (List.getElem?_eq_getElem inside : values[index]?=some values[index])
  obtain ⟨copied,copyRun,copyPC,heap,copyOld,copyAddress,copyFlag,total,index,value,output,memory⟩ :=
    bootstrapCopy_loop (calibrationInput P) values [] started
      rfl
      (by simp [started,bootstrapStartResult])
      (by simp [started,bootstrapStartResult])
      (by simpa only [size,rowWidth,Nat.mul_comm] using (show started.register .flag=.natural (P.certificate.M*2+3) by
        simp [started,bootstrapStartResult]))
      (by simp [HeapList,heapSegment]) data
  let after := bootstrapEndResult copied P.certificate.M
  have totalValue : copied.register .total=.natural P.certificate.M :=
    total.trans (by simp [started,bootstrapStartResult])
  have endRun : StandaloneSegment (calibrationInput P) copied after 120 :=
    bootstrapEnd_segment (calibrationInput P) copied P.certificate.M copyPC totalValue
  refine ⟨after,(((jumpRun.trans startRun).trans copyRun).trans endRun).mono ?_,rfl,?_,output,?_⟩
  · rw [size]
    unfold rowWidth
    omega
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [after,bootstrapEndResult,bootstrapEndBodyResult]
    · simp [after,bootstrapEndResult,bootstrapEndBodyResult]
    · simp [after,bootstrapEndResult,bootstrapEndBodyResult]
    · simpa [after,bootstrapEndResult,bootstrapEndBodyResult] using totalValue
    · simpa [after,bootstrapEndResult,bootstrapEndBodyResult] using
        index.trans (show started.register .index=.natural P.certificate.Q by simp [started,bootstrapStartResult])
    · simpa [after,bootstrapEndResult,bootstrapEndBodyResult] using
        value.trans (show started.register .value=.rational P.certificate.gamma by simp [started,bootstrapStartResult])
    · simpa only [List.nil_append,after,bootstrapEndResult,bootstrapEndBodyResult,HeapList,heapSegment] using heap
    · apply Finset.disjoint_left.mpr
      intro address alive inside
      obtain ⟨offset,_bound,addressEq⟩ := Finset.mem_image.mp inside
      have lower : rowWidth P.certificate.M≤address := by
        rw [←addressEq]
        exact Nat.le_add_right _ _
      have outside : address∉Finset.range (([] : List Cell).length+values.length) := by
        simp only [List.length_nil,Nat.zero_add,Finset.mem_range,size]
        omega
      change address∈copied.live at alive
      have initialLive := (memory.2 address outside).mp alive
      exact Finset.notMem_empty address (by simpa only [started,bootstrapStartResult,entered,empty] using initialLive)
  · apply Finset.ext
    intro address
    constructor
    · intro alive
      change address∈copied.live at alive
      by_contra outside
      have notRange : address∉Finset.range (([] : List Cell).length+values.length) := by
        simpa only [List.length_nil,Nat.zero_add,size] using outside
      have initialLive := (memory.2 address notRange).mp alive
      exact Finset.notMem_empty address (by simpa only [started,bootstrapStartResult,entered,empty] using initialLive)
    · intro inside
      have bound : address<([]++values).length := by simpa only [List.nil_append,size,Finset.mem_range] using inside
      simpa only [Nat.zero_add,after,bootstrapEndResult,bootstrapEndBodyResult] using heap.1 address bound

end PDLower.CalibrationCompute
