module
public import Paid.PDCompute_Pack_Layout_001
public import Paid.PDMenu_ComputeFrame_009

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem writeRegion_subset_workspace (base n k : ℕ) : writeRegion base n k ⊆ workspace base n k := by
  intro address member
  rcases Finset.mem_union.mp member with header|result
  · obtain ⟨offset,inside,rfl⟩:=Finset.mem_image.mp header
    have bound:=Finset.mem_range.mp inside
    apply Finset.mem_image.mpr
    refine ⟨offset,Finset.mem_range.mpr ?_,rfl⟩
    unfold workspaceSize
    omega
  · obtain ⟨offset,inside,rfl⟩:=Finset.mem_image.mp result
    have bound:=Finset.mem_range.mp inside
    apply Finset.mem_image.mpr
    refine ⟨headerWords+entryWords*PDCompute.Solver.entryCount n k+offset,Finset.mem_range.mpr ?_,?_⟩
    · unfold workspaceSize
      omega
    · unfold resultBase tableBase
      omega

/-- Geometric inclusion alone, with no whole-world caller-live
disjointness, turns the precise actual footprint into the original frame. -/
theorem precise_frame (before after : State) (base n k : ℕ)
    (memory : MemoryFrame (writeRegion base n k) before after) : Frame before after base n k := by
  refine ⟨?_,?_⟩
  · intro address outside
    exact memory.1 address (fun inside=>outside (writeRegion_subset_workspace base n k inside))
  · intro address outside
    exact memory.2 address (fun inside=>outside (writeRegion_subset_workspace base n k inside))

end PDCompute.Pack
