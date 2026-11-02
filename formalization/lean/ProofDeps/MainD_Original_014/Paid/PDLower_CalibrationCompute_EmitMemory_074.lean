module

public import Paid.PDLower_CalibrationCompute_EmitCorrect_052
public import Paid.PDLower_CalibrationCompute_SumMemory_061
public import Paid.PDROC_CalibrationRow_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

theorem emitLead_memoryFrame (region : Finset ℕ) (before : State) (base cursor : ℕ) (q weight : ℚ)
    (first : cursor∈region) (second : cursor+1∈region) :
    MemoryFrame region before (emitLeadResult before base cursor q weight) := by
  have different (address : ℕ) (outside : address∉region) : address≠cursor ∧ address≠cursor+1 := by
    constructor
    · intro equal; exact outside (equal.symm ▸ first)
    · intro equal; exact outside (equal.symm ▸ second)
  constructor
  · intro address outside
    simp only [emitLeadResult,loadSlotResult,Function.update_apply,(different address outside).1,
      (different address outside).2,ite_false]
  · intro address outside
    simp only [emitLeadResult,loadSlotResult,Finset.mem_insert,(different address outside).1,
      (different address outside).2,false_or]

/-- The two output-cache stores and both real header updates are the
entire write footprint of emit, allowing outer endpoint-cache framing. -/
theorem emit_memoryFrame (region : Finset ℕ) (before : State) (base cursor level : ℕ) (q weight : ℚ)
    (first : cursor∈region) (second : cursor+1∈region)
    (levelCell : base+5∈region) (cursorCell : base+15∈region) :
    MemoryFrame region before (emitResult before base cursor level q weight) := by
  have lead := emitLead_memoryFrame region before base cursor q weight first second
  have updateCursor := storeSlotResult_memoryFrame region (emitLeadResult before base cursor q weight)
    base 15 .index cursorCell
  have updateLevel := incrementSlotResult_memoryFrame region
    (storeSlotResult (emitLeadResult before base cursor q weight) base 15 .index) base 5 level levelCell
  exact (lead.trans updateCursor).trans updateLevel

theorem workspace_member (base M offset : ℕ) (inside : offset<workspaceSize M) :
    base+offset∈workspace base M :=
  Finset.mem_image.mpr ⟨offset,Finset.mem_range.mpr inside,rfl⟩

theorem memoryFrame_enlarge {small large : Finset ℕ} {before after : State}
    (subset : small⊆large) (frame : MemoryFrame small before after) : MemoryFrame large before after :=
  ⟨fun address outside => frame.1 address (fun inside => outside (subset inside)),
   fun address outside => frame.2 address (fun inside => outside (subset inside))⟩

theorem rowRegion_subset_workspace (base M : ℕ) :
    PDROC.CalibrationRow.region base M⊆workspace base M := by
  intro address inside
  have bounds := (PDROC.CalibrationRow.mem_region base M address).mp inside
  have lower : base≤address := by rcases bounds with header|rows <;> omega
  apply Finset.mem_image.mpr
  refine ⟨address-base,Finset.mem_range.mpr ?_,by omega⟩
  unfold workspaceSize
  unfold resultBase at bounds
  omega

theorem rowFrame_workspace {before after : State} {base M : ℕ}
    (frame : MemoryFrame (PDROC.CalibrationRow.region base M) before after) : Frame before after base M :=
  memoryFrame_enlarge (rowRegion_subset_workspace base M) frame

theorem sumFrame_workspace {before after : State} {base M : ℕ}
    (frame : MemoryFrame (sumRegion base) before after) : Frame before after base M := by
  apply memoryFrame_enlarge ?_ frame
  intro address inside
  simp only [sumRegion,Finset.mem_insert,Finset.mem_singleton] at inside
  rcases inside with rfl|rfl
  · exact workspace_member base M 7 (by rw [workspaceSize_linear]; omega)
  · exact workspace_member base M 11 (by rw [workspaceSize_linear]; omega)

theorem emit_frame (before : State) (base M cursor level : ℕ) (q weight : ℚ)
    (first : cursor∈workspace base M) (second : cursor+1∈workspace base M) :
    Frame before (emitResult before base cursor level q weight) base M :=
  emit_memoryFrame (workspace base M) before base cursor level q weight first second
    (workspace_member base M 5 (by rw [workspaceSize_linear]; omega))
    (workspace_member base M 15 (by rw [workspaceSize_linear]; omega))

end PDLower.CalibrationCompute
