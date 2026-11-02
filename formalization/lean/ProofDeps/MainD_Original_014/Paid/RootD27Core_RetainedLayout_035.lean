module

public import Paid.RootD27Core_HeapSolverCall_031
public import Paid.RootD27Core_HeapCopy_034

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- Two reusable buffers strictly above the actual complete solver
workspace. The flag is a static call-site choice, never runtime code. -/
def retainedTableBase (base n k : ℕ) (upper : Bool) : ℕ :=
  base+(if upper then 70 else 62)*PDCompute.Solver.entryCount n k

def retainedTableCapacity (n k : ℕ) : ℕ := 8*PDCompute.Solver.entryCount n k

theorem retained_capacity_positive (n k : ℕ) : 0<PDCompute.Solver.entryCount n k := by
  unfold PDCompute.Solver.entryCount
  positivity

theorem original_table_capacity (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)).length≤resultCapacity n k :=
  PDCompute.Pack.encoding_capacity _ n k (originalTable_rows P fee penalty n k) (originalTable_columns P fee penalty n k)

theorem retained_capacity_enough (n k : ℕ) : resultCapacity n k≤retainedTableCapacity n k := by
  unfold resultCapacity retainedTableCapacity PDCompute.Solver.entryCount
  nlinarith

theorem retained_base_above_workspace (base n k : ℕ) (upper : Bool) :
    base+workspaceSize n k≤retainedTableBase base n k upper := by
  have bound:=workspaceSize_linear n k
  cases upper <;> simp only [retainedTableBase,Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem original_table_before_retained (P : Parameters) (fee penalty : ℚ) (base n k : ℕ) (upper : Bool) :
    resultBase base n k+(encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)).length≤
      retainedTableBase base n k upper := by
  calc
    _≤resultBase base n k+resultCapacity n k:=Nat.add_le_add_left (original_table_capacity P fee penalty n k) _
    _=base+workspaceSize n k:=by unfold resultBase tableBase workspaceSize;omega
    _≤retainedTableBase base n k upper:=retained_base_above_workspace base n k upper

theorem retained_outside_workspace (base n k offset : ℕ) (upper : Bool) :
    retainedTableBase base n k upper+offset∉workspace base n k := by
  have lower:=retained_base_above_workspace base n k upper
  intro member
  obtain ⟨index,inside,equal⟩:=Finset.mem_image.mp member
  have bound:=Finset.mem_range.mp inside
  omega

theorem retained_buffer_survives_solver {before after : State} (base n k : ℕ) (upper : Bool) (cells : List Cell)
    (stored : HeapList before (retainedTableBase base n k upper) cells)
    (frame : Frame before after base n k) : HeapList after (retainedTableBase base n k upper) cells :=
  PDLower.CalibrationCompute.HeapList.memoryFrame stored _ frame
    (fun offset _inside=>retained_outside_workspace base n k offset upper)

theorem retained_buffers_separate (base n k : ℕ) :
    retainedTableBase base n k false+retainedTableCapacity n k=retainedTableBase base n k true := by
  simp only [retainedTableBase,retainedTableCapacity,Bool.false_eq_true,ite_false,ite_true]
  omega

theorem retained_other_buffer_survives_copy {before after : State} (base n k count : ℕ) (written kept : Bool)
    (different : written≠kept) (cells : List Cell) (length : cells.length≤retainedTableCapacity n k)
    (countBound : count≤retainedTableCapacity n k)
    (stored : HeapList before (retainedTableBase base n k kept) cells)
    (memory : RegionMemory before after (cellRegion (retainedTableBase base n k written) count)) :
    HeapList after (retainedTableBase base n k kept) cells := by
  apply PDLower.CalibrationCompute.HeapList.regionMemory stored memory
  intro offset inside
  rw [mem_cellRegion_iff]
  cases written <;> cases kept
  · exact False.elim (different rfl)
  · simp only [retainedTableBase,retainedTableCapacity,Bool.false_eq_true,ite_false,ite_true] at *
    omega
  · simp only [retainedTableBase,retainedTableCapacity,Bool.false_eq_true,ite_false,ite_true] at *
    omega
  · exact False.elim (different rfl)

end RootD27.Core
