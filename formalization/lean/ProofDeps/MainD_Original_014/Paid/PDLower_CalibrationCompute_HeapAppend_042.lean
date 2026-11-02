module

public import Paid.PDLower_CalibrationCompute_HeapList_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- Extend the real heap representation by one cell, permitting arbitrary
old contents at the newly written position. -/
theorem HeapList.appendCell {before : State} {base : ℕ} {values : List Cell}
    (represented : HeapList before base values) (value : Cell) :
    HeapList (writeCell before (base+values.length) value) base (values++[value]) := by
  apply HeapList.of_values
  · intro index inside
    by_cases old : index<values.length
    · exact Finset.mem_insert_of_mem (represented.1 index old)
    · have bound : index<values.length+1 := by simpa only [List.length_append,List.length_singleton] using inside
      have last : index=values.length := by omega
      subst index
      exact Finset.mem_insert_self _ _
  · intro index inside
    by_cases old : index<values.length
    · have separate : base+index ≠ base+values.length := by omega
      simp only [writeCell,Function.update_apply,separate,↓reduceIte]
      rw [List.getElem_append_left old]
      exact HeapList.value represented index old
    · have bound : index<values.length+1 := by simpa only [List.length_append,List.length_singleton] using inside
      have last : index=values.length := by omega
      subst index
      simp [writeCell]

end PDLower.CalibrationCompute
