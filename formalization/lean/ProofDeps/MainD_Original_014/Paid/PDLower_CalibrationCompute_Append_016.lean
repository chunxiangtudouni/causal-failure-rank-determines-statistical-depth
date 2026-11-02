module

public import Paid.PDLower_CalibrationCompute_HeapList_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem writeCell_execute_registers (input : List Cell) (state : State) (address : ℕ) (value : Cell)
    (pointer source : Register) (pointerValue : state.register pointer = .natural address)
    (sourceValue : state.register source = value) :
    Instruction.execute input (.store pointer source) state = some (writeCell state address value) := by
  simp [Instruction.execute,pointerValue,sourceValue,Cell.nat?,writeCell]

theorem HeapList.snoc {state : State} {base : ℕ} {values : List Cell}
    (represented : HeapList state base values) (value : Cell) :
    HeapList (writeCell state (base+values.length) value) base (values++[value]) := by
  apply HeapList.of_values
  · intro query inside
    by_cases old : query < values.length
    · exact Finset.mem_insert_of_mem (represented.1 query old)
    · have eq : query = values.length := by simp only [List.length_append,List.length_cons,List.length_nil] at inside; omega
      subst query
      exact Finset.mem_insert_self (base+values.length) state.live
  · intro query inside
    simp only [writeCell,Function.update_apply]
    by_cases old : query < values.length
    · have different : base+query ≠ base+values.length := by omega
      rw [ite_eq_right different,List.getElem_append_left old]
      exact HeapList.value represented query old
    · have eq : query = values.length := by simp only [List.length_append,List.length_cons,List.length_nil] at inside; omega
      subst query
      rw [ite_eq_left rfl,List.getElem_append_right (Nat.le_refl _)]
      simp

end PDLower.CalibrationCompute
