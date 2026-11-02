module

public import Paid.PDCompute_SolverReadRegion_093

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation

theorem headerRegion_subset_workspace (base n k : ℕ) : cellRegion base headerWords ⊆ workspace base n k := by
  have capacity : headerWords ≤ workspaceSize n k := by unfold workspaceSize; omega
  intro address member
  have bounds:=(mem_cellRegion_iff base headerWords address).mp member
  exact Finset.mem_image.mpr ⟨address-base,Finset.mem_range.mpr (by omega),by omega⟩

theorem HeaderMemory.region {before after : State} {base : ℕ} (memory : HeaderMemory before after base)
    (region : Finset ℕ) (included : cellRegion base headerWords ⊆ region) : RegionMemory before after region := by
  refine ⟨?_,?_,?_,memory.2.2⟩
  · intro address outside
    have outsideHeader : address ∉ cellRegion base headerWords := fun member => outside (included member)
    have beyond : address < base ∨ base+headerWords ≤ address := by
      rw [mem_cellRegion_iff] at outsideHeader
      omega
    exact memory.1 address beyond
  · rw [memory.2.1]
    exact Finset.subset_union_left
  · simpa only [memory.2.1] using Finset.Subset.refl before.live

theorem HeaderMemory.frame {before after : State} {base : ℕ} (memory : HeaderMemory before after base) (n k : ℕ) :
    Frame before after base n k :=
  (memory.region (cellRegion base headerWords) (Finset.Subset.refl _)).frame (headerRegion_subset_workspace base n k)

theorem RegionMemory.heapList {before after : State} {region : Finset ℕ} {pointer : ℕ} {cells : List Cell}
    (memory : RegionMemory before after region) (source : PDLower.CalibrationCompute.HeapList before pointer cells)
    (outside : ∀ offset < cells.length,pointer+offset ∉ region) :
    PDLower.CalibrationCompute.HeapList after pointer cells := by
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset bound
    exact memory.2.2.1 (source.1 offset bound)
  · intro offset bound
    rw [memory.1 _ (outside offset bound)]
    exact PDLower.CalibrationCompute.HeapList.value source offset bound

theorem HeaderMemory.heapList {before after : State} {base pointer : ℕ} {cells : List Cell}
    (memory : HeaderMemory before after base) (source : PDLower.CalibrationCompute.HeapList before pointer cells)
    (outside : ∀ offset < cells.length,pointer+offset < base ∨ base+headerWords ≤ pointer+offset) :
    PDLower.CalibrationCompute.HeapList after pointer cells := by
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset bound
    rw [memory.2.1]
    exact source.1 offset bound
  · intro offset bound
    rw [memory.1 _ (outside offset bound)]
    exact PDLower.CalibrationCompute.HeapList.value source offset bound

end PDCompute.Solver
