module
public import Paid.PDCompute_Pack_MemoryJoin_015
public import Paid.PDLower_CalibrationCompute_HeapList_010

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation 
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

def localRegion (base pointer count : ℕ) : Finset ℕ:=headerRegion base∪cellRegion pointer count

theorem headerMemory_local {before after : State} (base pointer count : ℕ)
    (memory : HeaderMemory before after base) : RegionMemory before after (localRegion base pointer count) := by
  refine ⟨?_,?_,?_,memory.2.2⟩
  · intro address outside
    have notHeader : address∉headerRegion base:=fun member=>outside (Finset.mem_union_left _ member)
    rw [headerRegion_eq,mem_cellRegion_iff] at notHeader
    exact memory.1 address (by omega)
  · rw [memory.2.1]
    exact Finset.subset_union_left
  · rw [memory.2.1]

theorem emissionMemory_local {before after : State} (base pointer count : ℕ)
    (memory : RegionMemory before after (cellRegion pointer count)) :
    RegionMemory before after (localRegion base pointer count) :=
  memory.enlarge Finset.subset_union_right

theorem localRegion_write_subset (base n k pointer count : ℕ)
    (lower : resultBase base n k ≤ pointer)
    (upper : pointer+count ≤ resultBase base n k+resultCapacity n k) :
    localRegion base pointer count ⊆ writeRegion base n k := by
  apply Finset.union_subset
  · exact Finset.subset_union_left
  · exact emission_region_subset base n k pointer count lower upper

theorem _root_.PDLower.CalibrationCompute.HeapList.regionMemory {before after : State} {pointer : ℕ} {cells : List Cell} {region : Finset ℕ}
    (heap : HeapList before pointer cells) (memory : RegionMemory before after region)
    (outside : ∀ offset<cells.length,pointer+offset∉region) : HeapList after pointer cells := by
  apply HeapList.of_values
  · intro offset bound
    exact memory.2.2.1 (heap.1 offset bound)
  · intro offset bound
    rw [memory.1 (pointer+offset) (outside offset bound)]
    exact heap.value offset bound

theorem _root_.PDLower.CalibrationCompute.HeapList.append {state : State} {pointer : ℕ} {first later : List Cell}
    (left : HeapList state pointer first) (right : HeapList state (pointer+first.length) later) :
    HeapList state pointer (first++later) := by
  apply HeapList.of_values
  · intro offset bound
    by_cases earlier : offset<first.length
    · exact left.1 offset earlier
    · have laterBound : offset-first.length<later.length := by simp only [List.length_append] at bound;omega
      have live:=right.1 (offset-first.length) laterBound
      simpa only [show pointer+first.length+(offset-first.length)=pointer+offset by omega] using live
  · intro offset bound
    by_cases earlier : offset<first.length
    · rw [List.getElem_append_left earlier]
      exact left.value offset earlier
    · have laterBound : offset-first.length<later.length := by simp only [List.length_append] at bound;omega
      rw [List.getElem_append_right (Nat.le_of_not_gt earlier)]
      have value:=right.value (offset-first.length) laterBound
      simpa only [show pointer+first.length+(offset-first.length)=pointer+offset by omega] using value

end PDCompute.Pack
