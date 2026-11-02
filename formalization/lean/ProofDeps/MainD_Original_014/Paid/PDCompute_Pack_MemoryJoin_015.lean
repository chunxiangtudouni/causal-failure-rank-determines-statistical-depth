module
public import Paid.PDCompute_Pack_Layout_001
public import Paid.PDCompute_SolverDenseWriteBlock_077

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver

theorem headerRegion_eq (base : ℕ) : headerRegion base=cellRegion base headerWords := rfl
theorem resultRegion_eq (base n k : ℕ) :
    resultRegion base n k=cellRegion (resultBase base n k) (resultCapacity n k) := rfl

/-- Scalar/header legs lift to the same precise footprint as emissions.
No live-disjointness is required: header cells already belong to caller. -/
theorem headerMemory_region {before after : State} (base n k : ℕ)
    (memory : HeaderMemory before after base) : RegionMemory before after (writeRegion base n k) := by
  refine ⟨?_,?_,?_,memory.2.2⟩
  · intro address outside
    have notHeader : address∉headerRegion base := fun member=>outside (Finset.mem_union_left _ member)
    rw [headerRegion_eq,mem_cellRegion_iff] at notHeader
    exact memory.1 address (by omega)
  · rw [memory.2.1]
    exact Finset.subset_union_left
  · rw [memory.2.1]

theorem emission_region_subset (base n k pointer count : ℕ)
    (lower : resultBase base n k≤pointer)
    (upper : pointer+count≤resultBase base n k+resultCapacity n k) :
    cellRegion pointer count ⊆ writeRegion base n k := by
  intro address member
  apply Finset.mem_union_right
  rw [resultRegion_eq,mem_cellRegion_iff]
  have inside:=(mem_cellRegion_iff pointer count address).mp member
  omega

theorem emission_memory_region {before after : State} (base n k pointer count : ℕ)
    (lower : resultBase base n k≤pointer)
    (upper : pointer+count≤resultBase base n k+resultCapacity n k)
    (memory : RegionMemory before after (cellRegion pointer count)) :
    RegionMemory before after (writeRegion base n k) :=
  memory.enlarge (emission_region_subset base n k pointer count lower upper)

end PDCompute.Pack
