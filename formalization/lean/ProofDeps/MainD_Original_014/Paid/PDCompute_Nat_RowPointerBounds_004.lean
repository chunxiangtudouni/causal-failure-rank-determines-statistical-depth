module
public import Paid.PDCompute_Pack_NaturalCap_054
public import Paid.PDCompute_SolverRowPointers_086

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PDCompute.Solver PDCompute.Pack

/-- All actual intermediates of original086, including the row0
provisional pointer and tool0 subtraction into Header42. Bounds do not
assert that either provisional pointer is read as a dense entry. -/
structure RowPointerBounds (base n k row column : ℕ) : Prop where
  predecessor : row-1≤naturalCap base n k
  columns : k+1≤naturalCap base n k
  product : (row-1)*(k+1)≤naturalCap base n k
  index : (row-1)*(k+1)+column≤naturalCap base n k
  scaled : 6*((row-1)*(k+1)+column)≤naturalCap base n k
  offset : 48+6*((row-1)*(k+1)+column)≤naturalCap base n k
  good : cellBase base k (row-1) column≤naturalCap base n k
  bad : cellBase base k (row-1) column-6≤naturalCap base n k
  stride : 6*(k+1)≤naturalCap base n k
  destination : cellBase base k (row-1) column+6*(k+1)≤naturalCap base n k

theorem baseHeader_le_cap (base n k : ℕ) : base+headerWords≤naturalCap base n k := by
  unfold naturalCap workspaceSize
  omega

theorem rowPointerBounds (base n k row column : ℕ) (rowBound : row≤n) (columnBound : column≤k) :
    RowPointerBounds base n k row column := by
  have predBound : row-1≤n:=by omega
  have productBound : (row-1)*(k+1)≤n*(k+1):=Nat.mul_le_mul_right (k+1) predBound
  have expanded : (n+1)*(k+1)=n*(k+1)+(k+1):=by ring
  have indexBound : (row-1)*(k+1)+column≤(n+1)*(k+1):=by omega
  have productCap : (row-1)*(k+1)≤(n+1)*(k+1):=by omega
  have scaledBound : 6*((row-1)*(k+1)+column)≤6*((n+1)*(k+1)):=Nat.mul_le_mul_left 6 indexBound
  have goodBound : cellBase base k (row-1) column≤resultBase base n k:=by
    change base+48+6*((row-1)*(k+1)+column)≤base+48+6*((n+1)*(k+1))
    omega
  have strideCapacity : 6*(k+1)≤resultCapacity n k:=by
    have factor:=Nat.mul_le_mul_right (1+6*(k+1)) (by omega : 1≤n+1)
    simp only [one_mul] at factor
    unfold resultCapacity
    omega
  have strideCap : 6*(k+1)≤naturalCap base n k:=by
    have cap:=naturalCap_result_end base n k
    omega
  have destinationCap : cellBase base k (row-1) column+6*(k+1)≤naturalCap base n k:=by
    have cap:=naturalCap_result_end base n k
    omega
  have goodCap:=goodBound.trans (naturalCap_resultBase base n k)
  refine ⟨?_,naturalCap_columns base n k,productCap.trans (naturalCap_product base n k),
    indexBound.trans (naturalCap_product base n k),scaledBound.trans (naturalCap_times_six base n k),?_,goodCap,?_,strideCap,destinationCap⟩
  · exact predBound.trans ((Nat.le_add_right n 1).trans (naturalCap_rows base n k))
  · have bound:=naturalCap_plus_header base n k
    omega
  · exact (Nat.sub_le _ _).trans goodCap

end PDCompute.NatControl
