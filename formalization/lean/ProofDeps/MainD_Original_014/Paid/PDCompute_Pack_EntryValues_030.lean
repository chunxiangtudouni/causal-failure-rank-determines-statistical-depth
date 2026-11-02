module
public import Paid.PDCompute_Pack_ReadEntry_029

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver

def entryValues (entry : MenuEntry) (values : ℕ → Cell) (source : ℕ) : ℕ → Cell :=
  readTailValues (loadedEntryValues entry values) (source+6)

theorem entryValues_loaded_slot (entry : MenuEntry) (values : ℕ → Cell) (source offset : ℕ) (inside : offset<6) :
    entryValues entry values source (24+offset)=
      (denseEncodeEntry entry)[offset]'(by rw [denseEncodeEntry_length];exact inside) := by
  unfold entryValues readTailValues
  rw [Function.update_of_ne (by unfold sourceCursor;omega)]
  exact loaded_entry_slots entry values offset inside

theorem entryValues_preserves (entry : MenuEntry) (values : ℕ → Cell) (source slot : ℕ)
    (outside : slot<24 ∨ 30≤slot) (different : slot≠sourceCursor) :
    entryValues entry values source slot=values slot := by
  unfold entryValues readTailValues
  rw [Function.update_of_ne different]
  exact loaded_entry_preserves entry values slot outside

theorem entryValues_source (entry : MenuEntry) (values : ℕ → Cell) (source : ℕ) :
    entryValues entry values source sourceCursor=.natural (source+6) := by
  simp only [entryValues,readTailValues,Function.update_self]

theorem entryValues_payload (entry : MenuEntry) (values : ℕ → Cell) (source : ℕ) :
    (actionSlots entry.action).map (entryValues entry values source)=encodeEntry entry := by
  rw [←loaded_original_payload entry values]
  apply List.map_congr_left
  intro slot member
  have bounds:=selected_slots_inside entry.action slot member
  unfold entryValues readTailValues
  rw [Function.update_of_ne (by unfold sourceCursor;unfold entryStart at bounds;omega)]

end PDCompute.Pack
