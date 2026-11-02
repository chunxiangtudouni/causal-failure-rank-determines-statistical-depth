module

public import Paid.PDLower_CalibrationCompute_SumFrame_031
public import Paid.PDLower_CalibrationCompute_SumFinish_034
public import Paid.PDMenu_ComputeFrame_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

theorem HeapList.memoryFrame {before after : State} {start : ℕ} {values : List Cell}
    (represented : HeapList before start values) (region : Finset ℕ)
    (frame : MemoryFrame region before after)
    (separate : ∀ index<values.length,start+index∉region) : HeapList after start values := by
  apply HeapList.of_values
  · intro index inside
    exact (frame.2 (start+index) (separate index inside)).mpr (represented.1 index inside)
  · intro index inside
    exact (frame.1 (start+index) (separate index inside)).trans (HeapList.value represented index inside)

theorem storeSlotResult_memoryFrame (region : Finset ℕ) (before : State) (base offset : ℕ) (source : Register)
    (inside : base+offset∈region) : MemoryFrame region before (storeSlotResult before base offset source) := by
  have different (query : ℕ) (outside : query∉region) : query≠base+offset := by
    intro eq
    exact outside (eq.symm ▸ inside)
  constructor
  · intro query outside
    simp only [storeSlotResult,Function.update_apply,different query outside,ite_false]
  · intro query outside
    simp only [storeSlotResult,Finset.mem_insert,different query outside,false_or]

theorem incrementSlotResult_memoryFrame (region : Finset ℕ) (before : State) (base offset value : ℕ)
    (inside : base+offset∈region) : MemoryFrame region before (incrementSlotResult before base offset value) := by
  have unchanged : MemoryFrame region before (incrementSlotLoaded before base offset value) := .refl region before
  exact unchanged.trans (storeSlotResult_memoryFrame region _ base offset .index inside)

theorem constantSlotResult_memoryFrame (region : Finset ℕ) (before : State) (base offset : ℕ) (value : Cell)
    (inside : base+offset∈region) : MemoryFrame region before (constantSlotResult before base offset value) := by
  have unchanged : MemoryFrame region before ({before with pc:=before.pc+1}.set .value value) := .refl region before
  exact unchanged.trans (storeSlotResult_memoryFrame region _ base offset .value inside)

def sumRegion (base : ℕ) : Finset ℕ := {base+7,base+11}

theorem sumCell_memoryFrame (before : State) (base read cursor : ℕ) (q value : ℚ) :
    MemoryFrame (sumRegion base) before (sumCellResult before base read cursor q value) := by
  have lead : MemoryFrame (sumRegion base) before (sumCellLeadResult before base read cursor q value) := .refl _ before
  have sum := storeSlotResult_memoryFrame (sumRegion base) (sumCellLeadResult before base read cursor q value)
    base 11 .value (by simp [sumRegion])
  have increment := incrementSlotResult_memoryFrame (sumRegion base)
    (storeSlotResult (sumCellLeadResult before base read cursor q value) base 11 .value)
    base 7 cursor (by simp [sumRegion])
  exact (lead.trans sum).trans increment

theorem sumFinish_memoryFrame (before : State) (base read level : ℕ) (q center : ℚ) :
    MemoryFrame (sumRegion base) before (sumFinishResult before base read level q center) := by
  have lead : MemoryFrame (sumRegion base) before (sumFinishLeadResult before base read level q center) := .refl _ before
  exact lead.trans (storeSlotResult_memoryFrame (sumRegion base) _ base 11 .value (by simp [sumRegion]))

end PDLower.CalibrationCompute
