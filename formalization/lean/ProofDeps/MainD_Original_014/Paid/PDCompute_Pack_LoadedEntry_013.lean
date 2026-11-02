module
public import Paid.PDCompute_Pack_Code_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver

def loadedEntryValues (entry : MenuEntry) (values : ℕ → Cell) : ℕ → Cell :=
  denseReadHeaderValues (denseEncodeEntry entry) entryStart values

/-- These are the cell-map conclusions of the already verified real
six-cell loader, not premises about a desired serialized answer. -/
theorem loaded_entry_slots (entry : MenuEntry) (values : ℕ → Cell) (offset : ℕ) (inside : offset<6) :
    loadedEntryValues entry values (24+offset)=
      (denseEncodeEntry entry)[offset]'(by rw [denseEncodeEntry_length];exact inside) := by
  obtain ⟨action,observation,repairs,failure⟩:=entry
  cases action <;> interval_cases offset <;>
    simp [loadedEntryValues,denseEncodeEntry,denseReadHeaderValues,entryStart]

theorem loaded_entry_preserves (entry : MenuEntry) (values : ℕ → Cell) (slot : ℕ)
    (outside : slot<24 ∨ 30≤slot) : loadedEntryValues entry values slot=values slot := by
  have h24 : slot≠24 := by omega
  have h25 : slot≠25 := by omega
  have h26 : slot≠26 := by omega
  have h27 : slot≠27 := by omega
  have h28 : slot≠28 := by omega
  have h29 : slot≠29 := by omega
  obtain ⟨action,observation,repairs,failure⟩:=entry
  cases action <;>
    simp [loadedEntryValues,denseEncodeEntry,denseReadHeaderValues,entryStart,h24,h25,h26,h27,h28,h29]

theorem loaded_original_payload (entry : MenuEntry) (values : ℕ → Cell) :
    (actionSlots entry.action).map (loadedEntryValues entry values)=encodeEntry entry := by
  obtain ⟨action,observation,repairs,failure⟩:=entry
  cases action <;>
    simp [loadedEntryValues,actionSlots,denseEncodeEntry,denseReadHeaderValues,entryStart,encodeEntry,encodeAction]

end PDCompute.Pack
