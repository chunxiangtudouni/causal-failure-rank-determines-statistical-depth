module
public import Paid.RootD27Core_RetainedCopy_037
public import Paid.RootD27Endpoint_CachePrefix_030
public import Paid.PDROC_CalibrationRow_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreMemory
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver

def coreBase (M : ℕ) : ℕ:=99+2*M
def globalSpan (M n k : ℕ) : ℕ:=coreBase M+78*PDCompute.Solver.entryCount n k+(6*M+25)
def globalRegion (M n k : ℕ) : Finset ℕ:=cellRegion 0 (globalSpan M n k)

theorem globalSpan_exact (M n k : ℕ) : globalSpan M n k=124+8*M+78*PDCompute.Solver.entryCount n k:=by
  unfold globalSpan coreBase
  omega

theorem globalSpan_coarse (M n k : ℕ) : globalSpan M n k≤coreBase M+78*PDCompute.Solver.entryCount n k+25*(M+1):=by
  have actual:=PDLower.CalibrationCompute.workspaceSize_le M
  rw [PDLower.CalibrationCompute.workspaceSize_linear] at actual
  unfold globalSpan
  omega

theorem globalRegion_card (M n k : ℕ) : (globalRegion M n k).card=globalSpan M n k:=by
  simp [globalRegion,cellRegion]

theorem cellRegion_subset_global (M n k pointer count : ℕ) (ending : pointer+count≤globalSpan M n k) :
    cellRegion pointer count⊆globalRegion M n k:=by
  intro address member
  obtain ⟨_,upper⟩:=(mem_cellRegion_iff pointer count address).mp member
  exact (mem_cellRegion_iff 0 _ address).mpr ⟨Nat.zero_le _,by simpa only [Nat.zero_add] using upper.trans_le ending⟩

theorem prepared_subset_global (M n k : ℕ) : cellRegion 0 13⊆globalRegion M n k:=by
  apply cellRegion_subset_global
  unfold globalSpan coreBase
  omega

theorem metadata_subset_global (M n k : ℕ) : cellRegion 13 48⊆globalRegion M n k:=by
  apply cellRegion_subset_global
  unfold globalSpan coreBase
  omega

theorem copySlots_subset_global (M n k : ℕ) : ({46,47} : Finset ℕ)⊆globalRegion M n k:=by
  intro address member
  have bounds : address=46 ∨ address=47:=by simpa using member
  apply (mem_cellRegion_iff 0 _ address).mpr
  unfold globalSpan coreBase
  rcases bounds with rfl|rfl <;> omega

theorem endpointCache_subset_global (M n k : ℕ) : cellRegion 96 (PDLower.CalibrationCompute.rowWidth M)⊆globalRegion M n k:=by
  apply cellRegion_subset_global
  unfold globalSpan coreBase PDLower.CalibrationCompute.rowWidth
  omega

theorem endpointRegion_subset_global (M n k : ℕ) : RootD27.Endpoint.endpointLoopRegion 48 96 M⊆globalRegion M n k:=by
  apply Finset.union_subset
  · apply cellRegion_subset_global
    unfold globalSpan coreBase headerWords
    omega
  · exact endpointCache_subset_global M n k

theorem solverWorkspace_subset_global (M n k : ℕ) : workspace (coreBase M) n k⊆globalRegion M n k:=by
  change cellRegion (coreBase M) (workspaceSize n k)⊆_
  apply cellRegion_subset_global
  have actual:=workspaceSize_linear n k
  unfold globalSpan
  omega

theorem retainedBuffer_subset_global (M n k : ℕ) (upper : Bool) :
    cellRegion (RootD27.Core.retainedTableBase (coreBase M) n k upper) (RootD27.Core.retainedTableCapacity n k)⊆globalRegion M n k:=by
  apply cellRegion_subset_global
  cases upper <;> simp only [RootD27.Core.retainedTableBase,RootD27.Core.retainedTableCapacity,Bool.false_eq_true,ite_false,ite_true] <;>
    unfold globalSpan <;> omega

theorem retainedCopy_subset_global (M n k count : ℕ) (upper : Bool) (bound : count≤RootD27.Core.retainedTableCapacity n k) :
    RootD27.Core.retainedCopyRegion (coreBase M) n k count upper⊆globalRegion M n k:=by
  apply Finset.union_subset
  · exact copySlots_subset_global M n k
  · apply cellRegion_subset_global
    unfold RootD27.Core.retainedTableCapacity at bound
    cases upper <;> simp only [RootD27.Core.retainedTableBase,Bool.false_eq_true,ite_false,ite_true] <;>
      unfold globalSpan <;> omega

theorem calibrationWorkspace_subset_global (M n k : ℕ) :
    PDLower.CalibrationCompute.workspace (coreBase M) M⊆globalRegion M n k:=by
  change cellRegion (coreBase M) (PDLower.CalibrationCompute.workspaceSize M)⊆_
  apply cellRegion_subset_global
  rw [PDLower.CalibrationCompute.workspaceSize_linear]
  unfold globalSpan
  omega

/-- The REAL row-library write region contains five header words and
two rows; its result cache is the third row in the whole workspace. -/
theorem calibrationRow_subset_global (M n k : ℕ) : PDROC.CalibrationRow.region (coreBase M) M⊆globalRegion M n k:=by
  intro address member
  have actual:=(PDROC.CalibrationRow.mem_region (coreBase M) M address).mp member
  apply (mem_cellRegion_iff 0 _ address).mpr
  unfold PDLower.CalibrationCompute.resultBase PDLower.CalibrationCompute.rowWidth at actual
  unfold globalSpan
  rcases actual with header|rows <;> omega

theorem calibrationBuffers_subset_global (M n k : ℕ) :
    cellRegion (PDLower.CalibrationCompute.firstRow (coreBase M)) (PDLower.CalibrationCompute.rowWidth M) ∪
      cellRegion (PDLower.CalibrationCompute.secondRow (coreBase M) M) (PDLower.CalibrationCompute.rowWidth M) ∪
      cellRegion (PDLower.CalibrationCompute.resultBase (coreBase M) M) (PDLower.CalibrationCompute.rowWidth M)⊆globalRegion M n k:=by
  apply Finset.union_subset
  · apply Finset.union_subset
    · apply cellRegion_subset_global
      unfold PDLower.CalibrationCompute.firstRow PDLower.CalibrationCompute.rowWidth globalSpan
      omega
    · apply cellRegion_subset_global
      unfold PDLower.CalibrationCompute.secondRow PDLower.CalibrationCompute.rowWidth globalSpan
      omega
  · apply cellRegion_subset_global
    unfold PDLower.CalibrationCompute.resultBase PDLower.CalibrationCompute.rowWidth globalSpan
    omega

end PDCompute.CoreMemory
