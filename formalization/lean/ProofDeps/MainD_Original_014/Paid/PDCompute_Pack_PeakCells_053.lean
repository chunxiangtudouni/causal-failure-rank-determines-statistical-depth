module
public import Paid.PDCompute_Pack_Region_011
public import Paid.PDCompute_Pack_MemoryJoin_015

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver

theorem workspace_card_le (base n k : ℕ) : (workspace base n k).card ≤ workspaceSize n k := by
  unfold workspace
  exact Finset.card_image_le.trans (by rw [Finset.card_range])

theorem writeRegion_card_le (base n k : ℕ) : (writeRegion base n k).card ≤ workspaceSize n k :=
  (Finset.card_le_card (writeRegion_subset_workspace base n k)).trans (workspace_card_le base n k)

/-- Peak live-cell accounting allows arbitrary caller live cells already
inside either writable region. No global disjointness assumption is used. -/
theorem regionMemory_workingCells {before after : State} (base n k : ℕ)
    (memory : RegionMemory before after (writeRegion base n k)) :
    workingCells after ≤ workingCells before+62*PDCompute.Solver.entryCount n k := by
  have liveBound:=(Finset.card_le_card memory.2.1).trans (Finset.card_union_le before.live (writeRegion base n k))
  have regionBound:=writeRegion_card_le base n k
  have sizeBound:=workspaceSize_linear n k
  unfold workingCells
  rw [memory.2.2.2]
  omega

theorem foldl_max_bound (values : List ℕ) (seed bound : ℕ) (initial : seed ≤ bound)
    (members : ∀ value∈values,value ≤ bound) : values.foldl max seed ≤ bound := by
  induction values generalizing seed with
  | nil=>exact initial
  | cons value values ih=>
    apply ih (max seed value) (max_le initial (members value (by simp)))
    intro later member
    exact members later (by simp [member])

theorem prefix_region_peakCells (trace : List State) (before : State) (base n k : ℕ)
    (memory : ∀ state∈trace,RegionMemory before state (writeRegion base n k)) :
    peakCells trace ≤ workingCells before+62*PDCompute.Solver.entryCount n k := by
  apply foldl_max_bound _ 0 _ (Nat.zero_le _)
  intro size member
  obtain ⟨state,stateMember,rfl⟩:=List.mem_map.mp member
  exact regionMemory_workingCells base n k (memory state stateMember)

end PDCompute.Pack
