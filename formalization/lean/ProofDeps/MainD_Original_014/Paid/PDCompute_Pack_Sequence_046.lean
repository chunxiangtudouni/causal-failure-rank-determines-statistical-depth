module
public import Paid.PDCompute_Pack_LocalRegion_044
public import Paid.PDCompute_Pack_EntryAdvance_037
public import Paid.PDCompute_Pack_EntryValues_030

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation 
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

def encodedEntries (entries : List MenuEntry) : List Cell:=entries.flatMap encodeEntry
def denseEntries (entries : List MenuEntry) : List Cell:=entries.flatMap denseEncodeEntry

theorem denseEntries_length (entries : List MenuEntry) : (denseEntries entries).length=6*entries.length := by
  induction entries with
  | nil=>rfl
  | cons entry entries ih=>simp only [denseEntries,List.flatMap_cons,List.length_append,denseEncodeEntry_length,entryWords,List.length_cons] at ih ⊢;omega

theorem _root_.PDLower.CalibrationCompute.HeapList.append_left {state : State} {pointer : ℕ} {first later : List Cell}
    (heap : HeapList state pointer (first++later)) : HeapList state pointer first := by
  apply HeapList.of_values
  · intro offset bound
    exact heap.1 offset (by simp only [List.length_append];omega)
  · intro offset bound
    exact (heap.value offset (by simp only [List.length_append];omega)).trans (List.getElem_append_left bound)

theorem _root_.PDLower.CalibrationCompute.HeapList.append_right {state : State} {pointer : ℕ} {first later : List Cell}
    (heap : HeapList state pointer (first++later)) : HeapList state (pointer+first.length) later := by
  apply HeapList.of_values
  · intro offset bound
    have live:=heap.1 (first.length+offset) (by simp only [List.length_append];omega)
    simpa only [Nat.add_assoc] using live
  · intro offset bound
    have value:=heap.value (first.length+offset) (by simp only [List.length_append];omega)
    simpa only [Nat.add_assoc,List.getElem_append_right (by omega : first.length ≤ first.length+offset),Nat.add_sub_cancel_left] using value

theorem localRegion_left_subset (base pointer first later : ℕ) :
    localRegion base pointer first ⊆ localRegion base pointer (first+later) := by
  apply Finset.union_subset_union (Finset.Subset.refl _)
  intro address member
  rw [mem_cellRegion_iff] at member ⊢
  omega

theorem localRegion_right_subset (base pointer first later : ℕ) :
    localRegion base (pointer+first) later ⊆ localRegion base pointer (first+later) := by
  apply Finset.union_subset_union (Finset.Subset.refl _)
  intro address member
  rw [mem_cellRegion_iff] at member ⊢
  omega

def entryStable (slot : ℕ) : Prop:=(slot<24 ∨ 30 ≤ slot) ∧ slot≠columnRemaining ∧ slot≠sourceCursor ∧ slot≠outputCursor
def entryStepValues (entry : MenuEntry) (values : ℕ → Cell) (source pointer count : ℕ) : ℕ → Cell:=
  entryAdvanceValues (entryValues entry values source) (pointer+(encodeEntry entry).length) count

theorem entryStep_source (entry : MenuEntry) (values : ℕ → Cell) (source pointer count : ℕ) :
    entryStepValues entry values source pointer count sourceCursor=.natural (source+6) := by
  simp only [entryStepValues,entryAdvanceValues,Function.update_of_ne (by decide : sourceCursor≠columnRemaining),
    Function.update_of_ne (by decide : sourceCursor≠outputCursor),entryValues_source]
theorem entryStep_pointer (entry : MenuEntry) (values : ℕ → Cell) (source pointer count : ℕ) :
    entryStepValues entry values source pointer count outputCursor=.natural (pointer+(encodeEntry entry).length) := by
  simp only [entryStepValues,entryAdvanceValues,Function.update_of_ne (by decide : outputCursor≠columnRemaining),Function.update_self]
theorem entryStep_count (entry : MenuEntry) (values : ℕ → Cell) (source pointer count : ℕ) :
    entryStepValues entry values source pointer count columnRemaining=.natural (count-1) := by
  simp only [entryStepValues,entryAdvanceValues,Function.update_self]
theorem entryStep_stable (entry : MenuEntry) (values : ℕ → Cell) (source pointer count slot : ℕ)
    (stable : entryStable slot) : entryStepValues entry values source pointer count slot=values slot := by
  unfold entryStepValues entryAdvanceValues
  rw [Function.update_of_ne stable.2.1,Function.update_of_ne stable.2.2.2]
  exact entryValues_preserves entry values source slot stable.1 stable.2.2.1

end PDCompute.Pack
