module

public import Paid.RootD27Core_InputSlotRegion_019

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

def inputCopyCode : ℕ → List Instruction
  | 0 => []
  | count+1 => inputCopyCode count++inputSlotCode count

def inputCopyResult (input : List Cell) (before : State) : ℕ → State
  | 0 => before
  | count+1 => inputSlotResult (inputCopyResult input before count) count
      ((input[count]?).getD (.natural 0))

theorem inputCopy_length (count : ℕ) : (inputCopyCode count).length=3*count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [inputCopyCode,List.length_append,ih,inputSlot_length,Nat.mul_succ]

theorem inputCopy_pc (input : List Cell) (before : State) (count : ℕ) :
    (inputCopyResult input before count).pc=before.pc+3*count := by
  induction count with
  | zero => simp only [inputCopyResult,Nat.mul_zero,Nat.add_zero]
  | succ count ih =>
    change (inputCopyResult input before count).pc+3=_
    rw [ih]
    omega

theorem inputCopy_output (input : List Cell) (before : State) (count : ℕ) :
    (inputCopyResult input before count).output=before.output := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

theorem inputCopy_stored (input : List Cell) (before : State) (count : ℕ) :
    ∀ slot<count,slot∈(inputCopyResult input before count).live ∧
      (inputCopyResult input before count).heap slot=(input[slot]?).getD (.natural 0) := by
  induction count with
  | zero => intro slot inside; omega
  | succ count ih =>
    intro slot inside
    by_cases same : slot=count
    · subst slot
      exact ⟨Finset.mem_insert_self _ _,Function.update_self _ _ _⟩
    · have prior:=ih slot (by omega)
      refine ⟨Finset.mem_insert_of_mem prior.1,?_⟩
      change Function.update (inputCopyResult input before count).heap count
        ((input[count]?).getD (.natural 0)) slot=_
      rw [Function.update_of_ne same]
      exact prior.2

theorem inputCopy_heapList (input : List Cell) (before : State) (count : ℕ) :
    HeapList (inputCopyResult input before count) 0 (input.take count) := by
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset inside
    have bound : offset<count := lt_of_lt_of_le inside (List.length_take_le count input)
    simpa only [Nat.zero_add] using (inputCopy_stored input before count offset bound).1
  · intro offset inside
    have bound : offset<count := lt_of_lt_of_le inside (List.length_take_le count input)
    have fetched : input[offset]?=some (input.take count)[offset] := by
      rw [←List.getElem?_take_of_lt bound]
      exact List.getElem?_eq_getElem inside
    have value:=(inputCopy_stored input before count offset bound).2
    simpa only [Nat.zero_add,fetched,Option.getD_some] using value

end RootD27.Core
