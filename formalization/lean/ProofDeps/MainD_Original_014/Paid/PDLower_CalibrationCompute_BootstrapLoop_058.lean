module

public import Paid.PDLower_CalibrationCompute_StandaloneSegment_057
public import Paid.PDMenu_ComputeFrame_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

theorem bootstrapGate_execute (input : List Cell) (before : State) (remaining : ℕ)
    (position : before.pc=mainStart+12) (flag : before.register .flag=.natural remaining) :
    step calibrate input before=some {before with pc:=if remaining=0 then mainStart+20 else mainStart+13} := by
  have fetched : calibrate[before.pc]?=some (.branchZero .flag (mainStart+20) (mainStart+13)) := by
    rw [position,calibrate_bootstrap_fetch]
    rfl
  unfold step
  rw [fetched]
  change (Instruction.branchZero .flag (mainStart+20) (mainStart+13)).execute input before=_
  simp [Instruction.execute,flag,Cell.nat?]

/-- Actual copying of every original endpoint-input cell. The input
lookup premise names original cells, never a successful execution or a
preloaded heap. Each iteration includes its fetched gate and jump. -/
theorem bootstrapCopy_loop (input : List Cell) (tail doneCells : List Cell) (before : State)
    (position : before.pc=mainStart+12)
    (old : before.register .old=.natural (3+doneCells.length))
    (address : before.register .address=.natural doneCells.length)
    (flag : before.register .flag=.natural tail.length)
    (represented : HeapList before 0 doneCells)
    (data : ∀ (index : ℕ) (inside : index<tail.length),input[3+doneCells.length+index]?=some tail[index]) :
    ∃ after : State,StandaloneSegment input before after (150*tail.length+30) ∧
      after.pc=mainStart+20 ∧ HeapList after 0 (doneCells++tail) ∧
      after.register .old=.natural (3+(doneCells++tail).length) ∧
      after.register .address=.natural (doneCells++tail).length ∧ after.register .flag=.natural 0 ∧
      after.register .total=before.register .total ∧
      after.register .index=before.register .index ∧
      after.register .value=before.register .value ∧ after.output=before.output ∧
      MemoryFrame (Finset.range (doneCells.length+tail.length)) before after := by
  induction tail generalizing doneCells before with
  | nil =>
    let after : State := {before with pc:=mainStart+20}
    have actual : step calibrate input before=some after :=
      bootstrapGate_execute input before 0 position flag
    refine ⟨after,standalone_oneStep input before after actual,rfl,?_,?_,?_,flag,rfl,rfl,rfl,rfl,?_⟩
    · simpa only [List.append_nil,after,HeapList,heapSegment] using represented
    · simpa only [List.append_nil] using old
    · simpa only [List.append_nil] using address
    · exact MemoryFrame.refl _ before
  | cons value tail ih =>
    let entered : State := {before with pc:=mainStart+13}
    have actual : step calibrate input before=some entered := by
      simpa only [List.length_cons,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false] using
        bootstrapGate_execute input before (value::tail).length position flag
    have gate := standalone_oneStep input before entered actual
    have first : input[3+doneCells.length]?=some value := by
      have actual := data 0 (by simp)
      change input[3+doneCells.length+0]?=some value at actual
      simpa only [Nat.add_zero] using actual
    let next : State := {bootstrapCopyResult entered (3+doneCells.length) doneCells.length (value::tail).length value with pc:=mainStart+12}
    have cell : StandaloneSegment input entered next 120 :=
      bootstrapCopy_segment input entered (3+doneCells.length) doneCells.length (value::tail).length value rfl old address flag first
    have nextHeap : HeapList next 0 (doneCells++[value]) := by
      simpa only [next,bootstrapCopyResult,writeCell,Nat.zero_add,HeapList,heapSegment] using represented.appendCell value
    have nextOld : next.register .old=.natural (3+(doneCells++[value]).length) := by
      simp [next,bootstrapCopyResult,List.length_append,Nat.add_assoc]
    have nextAddress : next.register .address=.natural (doneCells++[value]).length := by
      simp [next,bootstrapCopyResult]
    have nextFlag : next.register .flag=.natural tail.length := by simp [next,bootstrapCopyResult]
    have nextData (index : ℕ) (inside : index<tail.length) :
        input[3+(doneCells++[value]).length+index]?=some tail[index] := by
      have following := data (index+1) (by simp only [List.length_cons]; omega)
      simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1,List.getElem_cons_succ] using following
    obtain ⟨after,later,pc,heap,finalOld,finalAddress,finalFlag,total,index,lastValue,output,memory⟩ :=
      ih (doneCells++[value]) next rfl nextOld nextAddress nextFlag nextHeap nextData
    refine ⟨after,((gate.trans cell).trans later).mono (by simp only [List.length_cons]; omega),pc,?_,?_,?_,finalFlag,total,index,lastValue,output,?_⟩
    · simpa only [List.append_assoc,List.singleton_append] using heap
    · simpa only [List.append_assoc,List.singleton_append] using finalOld
    · simpa only [List.append_assoc,List.singleton_append] using finalAddress
    · have inside : doneCells.length<doneCells.length+(value::tail).length := by
        simp only [List.length_cons]
        omega
      have different (query : ℕ) (outside : query∉Finset.range (doneCells.length+(value::tail).length)) :
          query≠doneCells.length := by
        intro equal
        apply outside
        rw [equal]
        exact Finset.mem_range.mpr inside
      have current : MemoryFrame (Finset.range (doneCells.length+(value::tail).length)) before next := by
        constructor
        · intro query outside
          simp only [next,bootstrapCopyResult,entered,Function.update_apply,different query outside,ite_false]
        · intro query outside
          simp only [next,bootstrapCopyResult,entered,Finset.mem_insert,different query outside,false_or]
      have size : (doneCells++[value]).length+tail.length=doneCells.length+(value::tail).length := by
        simp only [List.length_append,List.length_cons,List.length_nil]
        omega
      have following : MemoryFrame (Finset.range (doneCells.length+(value::tail).length)) next after := by
        simpa only [size] using memory
      exact current.trans following

end PDLower.CalibrationCompute
