module

public import Paid.PDCompute_SolverDenseWrite_075

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation

/-- A real finite write footprint, allowing preexisting live caller
cells inside it. This does not replace the program's execution proof. -/
def RegionMemory (before after : State) (region : Finset ℕ) : Prop :=
  (∀ address ∉ region, after.heap address=before.heap address) ∧
  after.live ⊆ before.live ∪ region ∧ before.live ⊆ after.live ∧ after.output=before.output

theorem RegionMemory.refl (before : State) (region : Finset ℕ) : RegionMemory before before region :=
  ⟨fun _ _ => rfl,Finset.subset_union_left,Finset.Subset.refl _,rfl⟩

theorem RegionMemory.trans {before middle after : State} {region : Finset ℕ}
    (first : RegionMemory before middle region) (later : RegionMemory middle after region) :
    RegionMemory before after region := by
  refine ⟨fun address outside => (later.1 address outside).trans (first.1 address outside),?_,
    first.2.2.1.trans later.2.2.1,later.2.2.2.trans first.2.2.2⟩
  intro address live
  rcases Finset.mem_union.mp (later.2.1 live) with middleLive|written
  · exact first.2.1 middleLive
  · exact Finset.mem_union_right _ written

theorem RegionMemory.enlarge {before after : State} {region larger : Finset ℕ}
    (memory : RegionMemory before after region) (subset : region ⊆ larger) :
    RegionMemory before after larger := by
  refine ⟨fun address outside => memory.1 address (fun member => outside (subset member)),?_,memory.2.2⟩
  exact memory.2.1.trans (Finset.union_subset_union (Finset.Subset.refl _) subset)

theorem CellWriteMemory.region {before after : State} {pointer : ℕ} {region : Finset ℕ}
    (memory : CellWriteMemory before after pointer) (inside : pointer ∈ region) :
    RegionMemory before after region := by
  refine ⟨?_,?_,memory.2.2⟩
  · intro address outside
    apply memory.1 address
    intro same
    exact outside (same.symm ▸ inside)
  · intro address live
    rcases Finset.mem_insert.mp (memory.2.1 live) with same|old
    · exact Finset.mem_union_right _ (same.symm ▸ inside)
    · exact Finset.mem_union_left _ old

theorem RegionMemory.trace_last {trace : List State} {before after : State} {region : Finset ℕ}
    (memory : ∀ state ∈ trace, RegionMemory before state region) (last : trace.getLast?=some after) :
    RegionMemory before after region :=
  memory after (List.mem_of_getLast? last)

theorem RegionMemory.frame {before after : State} {region : Finset ℕ} {base n k : ℕ}
    (memory : RegionMemory before after region) (subset : region ⊆ workspace base n k) :
    Frame before after base n k := by
  constructor
  · intro address outside
    exact memory.1 address (fun inside => outside (subset inside))
  · intro address outside
    constructor
    · intro live
      rcases Finset.mem_union.mp (memory.2.1 live) with old|written
      · exact old
      · exact False.elim (outside (subset written))
    · intro live
      exact memory.2.2.1 live

theorem RegionMemory.join_trace (first later : List State) (before middle : State) (region : Finset ℕ)
    (last : first.getLast?=some middle)
    (firstMemory : ∀ state ∈ first, RegionMemory before state region)
    (laterMemory : ∀ state ∈ later, RegionMemory middle state region) :
    ∀ state ∈ PDMenu.ComputeFrame.joinTrace first later, RegionMemory before state region := by
  have split := List.dropLast_append_getLast? middle (by rw [last]; simp)
  have middleMemory := RegionMemory.trace_last firstMemory last
  intro state member
  rcases List.mem_append.mp member with firstMember|laterMember
  · apply firstMemory state
    rw [← split]
    exact List.mem_append.mpr (Or.inl firstMember)
  · exact middleMemory.trans (laterMemory state laterMember)

def cellRegion (pointer count : ℕ) : Finset ℕ := (Finset.range count).image (pointer+·)

theorem mem_cellRegion_iff (pointer count address : ℕ) :
    address ∈ cellRegion pointer count ↔ pointer ≤ address ∧ address < pointer+count := by
  constructor
  · intro member
    obtain ⟨offset,inside,rfl⟩ := Finset.mem_image.mp member
    have bound:=Finset.mem_range.mp inside
    omega
  · intro bounds
    exact Finset.mem_image.mpr ⟨address-pointer,Finset.mem_range.mpr (by omega),by omega⟩

theorem cellRegion_tail_subset (pointer count : ℕ) :
    cellRegion (pointer+1) count ⊆ cellRegion pointer (count+1) := by
  intro address member
  apply (mem_cellRegion_iff pointer (count+1) address).mpr
  have bounds := (mem_cellRegion_iff (pointer+1) count address).mp member
  omega

end PDCompute.Solver
