module
public import Paid.PDCompute_Pack_Layout_001
public import PaperProofs.Paid.PDROC_DataBits_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PDCompute.Solver PDROC.DataBits

theorem natBits_increment (n : ℕ) : natBits (n+1)≤natBits n+1 := by
  have h:=natBits_add_le n 1
  have one : natBits 1=1 := by decide
  omega

/-- Scalar addresses grow only logarithmically in runtime n/k. This is
a numerical lemma, not an assumed bound on the executed prefix states. -/
theorem workspace_end_bits (base n k : ℕ) :
    natBits (base+workspaceSize n k) ≤ natBits base+natBits n+natBits k+8 := by
  have mono:=natBits_mono (Nat.add_le_add_left (workspaceSize_linear n k) base)
  have add:=natBits_add_le base (62*PDCompute.Solver.entryCount n k)
  have factor:=natBits_mul_le 62 (PDCompute.Solver.entryCount n k)
  have product:=natBits_mul_le (n+1) (k+1)
  have left:=natBits_increment n
  have right:=natBits_increment k
  have sixtyTwo : natBits 62=6 := by decide
  change natBits (PDCompute.Solver.entryCount n k) ≤ natBits (n+1)+natBits (k+1) at product
  omega

theorem address_bits (base n k address : ℕ) (inside : address≤base+workspaceSize n k) :
    natBits address≤natBits base+natBits n+natBits k+8 :=
  (natBits_mono inside).trans (workspace_end_bits base n k)

theorem origin_pc_bits (origin pc : ℕ) (inside : pc≤origin+233) :
    natBits pc≤natBits origin+8 := by
  have mono:=natBits_mono inside
  have add:=natBits_add_le origin 233
  have fixed : natBits 233=8 := by decide
  omega

theorem writeRegion_address_bound (base n k address : ℕ) (member : address∈writeRegion base n k) :
    address≤base+workspaceSize n k := by
  rcases Finset.mem_union.mp member with header|result
  · obtain ⟨offset,inside,eq⟩:=Finset.mem_image.mp header
    have bound:=Finset.mem_range.mp inside
    unfold workspaceSize
    omega
  · obtain ⟨offset,inside,eq⟩:=Finset.mem_image.mp result
    have bound:=Finset.mem_range.mp inside
    unfold resultBase tableBase at eq
    unfold workspaceSize
    omega

end PDCompute.Pack
