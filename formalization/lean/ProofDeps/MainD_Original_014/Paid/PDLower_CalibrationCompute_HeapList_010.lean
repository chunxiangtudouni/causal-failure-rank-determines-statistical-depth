module

public import Paid.PDLower_CalibrationCompute_Rows_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem HeapList.value {state : State} {base : ℕ} {values : List Cell} (represented : HeapList state base values)
    (index : ℕ) (inside : index < values.length) : state.heap (base+index) = values[index] := by
  have lookup := congrArg (fun cells : List Cell => cells[index]?) represented.2
  simpa [heapSegment,inside] using lookup

theorem HeapList.of_values (state : State) (base : ℕ) (values : List Cell)
    (live : ∀ index < values.length,base+index ∈ state.live)
    (correct : ∀ (index : ℕ) (inside : index < values.length),state.heap (base+index) = values[index]) :
    HeapList state base values := by
  refine ⟨live,?_⟩
  apply List.ext_getElem (by simp [heapSegment])
  intro index _ inside
  simpa [heapSegment] using correct index inside

theorem HeapList.write {state : State} {base : ℕ} {values : List Cell} (represented : HeapList state base values)
    (index : ℕ) (_inside : index < values.length) (value : Cell) :
    HeapList (writeCell state (base+index) value) base (values.set index value) := by
  apply HeapList.of_values
  · intro query bound
    have oldBound : query < values.length := by simpa using bound
    exact Finset.mem_insert_of_mem (represented.1 query oldBound)
  · intro query bound
    have oldBound : query < values.length := by simpa using bound
    simp only [writeCell,Function.update_apply]
    by_cases same : index = query
    · subst query
      rw [ite_eq_left rfl,List.getElem_set_self bound]
    · have different : base+query ≠ base+index := by
        intro eq
        exact same (Nat.add_left_cancel eq).symm
      rw [ite_eq_right different,List.getElem_set_ne same bound]
      exact HeapList.value represented query oldBound

theorem HeapList.writeOutside {state : State} {base : ℕ} {values : List Cell} (represented : HeapList state base values)
    (address : ℕ) (value : Cell) (separate : ∀ index < values.length,address ≠ base+index) :
    HeapList (writeCell state address value) base values := by
  apply HeapList.of_values
  · intro query inside
    exact Finset.mem_insert_of_mem (represented.1 query inside)
  · intro query inside
    simp only [writeCell,Function.update_apply]
    rw [ite_eq_right (Ne.symm (separate query inside))]
    exact HeapList.value represented query inside

theorem HeapList.storeSlot (input : List Cell) (state : State) (base : ℕ) (values : List Cell)
    (represented : HeapList state base values) (baseValue : state.register .fresh = .natural base)
    (index : ℕ) (inside : index < values.length) (source : Register) (safe : source ≠ .address) :
    ∃ after,linearExecute input (storeSlot index source) state = some after ∧
      HeapList after base (values.set index (state.register source)) := by
  refine ⟨storeSlotResult state base index source,storeSlot_execute input state base index source baseValue safe,?_⟩
  simpa only [HeapList,heapSegment,storeSlotResult,writeCell] using
    HeapList.write represented index inside (state.register source)

theorem HeapList.loadSlot (input : List Cell) (state : State) (base : ℕ) (values : List Cell)
    (represented : HeapList state base values) (baseValue : state.register .fresh = .natural base)
    (index : ℕ) (inside : index < values.length) (target : Register) :
    ∃ after,linearExecute input (loadSlot index target) state = some after ∧ after.register target = values[index] := by
  refine ⟨loadSlotResult state base index target,
    loadSlot_execute input state base index target baseValue (represented.1 index inside),?_⟩
  simpa [loadSlotResult] using HeapList.value represented index inside

end PDLower.CalibrationCompute
