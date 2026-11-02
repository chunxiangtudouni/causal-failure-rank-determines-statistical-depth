module
public import Paid.PDCompute_Pack_EntryValues_030

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver

theorem entryValues_tag (entry : MenuEntry) (values : ℕ → Cell) (source : ℕ) :
    entryValues entry values source 24=.natural (entryTag entry) := by
  unfold entryValues readTailValues
  rw [Function.update_of_ne (by decide : (24:ℕ)≠sourceCursor)]
  exact loadedEntry_tag entry values

theorem entryValues_observation (entry : MenuEntry) (values : ℕ → Cell) (source : ℕ) :
    entryValues entry values source 27=.rational entry.observation := by
  have h:=entryValues_loaded_slot entry values source 3 (by decide)
  obtain ⟨action,observation,repairs,failure⟩:=entry
  cases action <;> simpa [denseEncodeEntry] using h

theorem entryValues_repairs (entry : MenuEntry) (values : ℕ → Cell) (source : ℕ) :
    entryValues entry values source 28=.rational entry.repairs := by
  have h:=entryValues_loaded_slot entry values source 4 (by decide)
  obtain ⟨action,observation,repairs,failure⟩:=entry
  cases action <;> simpa [denseEncodeEntry] using h

theorem entryValues_failure (entry : MenuEntry) (values : ℕ → Cell) (source : ℕ) :
    entryValues entry values source 29=.rational entry.failure := by
  have h:=entryValues_loaded_slot entry values source 5 (by decide)
  obtain ⟨action,observation,repairs,failure⟩:=entry
  cases action <;> simpa [denseEncodeEntry] using h

end PDCompute.Pack
