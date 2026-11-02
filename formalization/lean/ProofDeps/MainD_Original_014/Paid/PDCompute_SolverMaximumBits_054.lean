module

public import PaperProofs.Paid.ComputationalClaims
public import PaperProofs.Paid.PDROC_DataBits_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits

theorem maximumMenuBits_bound (P : Parameters) (fee : ℚ) :
    P.MenuEncodingBound fee (maximumMenuBits P fee) := by
  have nonempty : (P.menuScalars fee).map ratEncodingBits ≠ [] := by
    intro empty
    have size := congrArg List.length empty
    simp only [List.length_map,List.length_nil] at size
    have sourceSize := menuScalars_length P fee
    omega
  unfold maximumMenuBits
  rw [List.foldl_max_eq_max nonempty]
  refine ⟨le_max_left _ _,?_⟩
  intro scalar member
  exact (List.le_max_of_mem (List.mem_map.mpr ⟨scalar,member,rfl⟩)).trans (le_max_right _ _)

/-- General tools/stages, rather than the P.N/P.K specialization of the
paper's displayed table bound. Standalone solver inputs remain arbitrary. -/
theorem arbitraryTable_entry_denBits (P : Parameters) (fee penalty : ℚ) (stages tools row column : ℕ)
    (inside : row ≤ stages) :
    let entry := menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty tools stages) row column
    let scale := (row+1)*(2*(P.certificate.M+1)+2)*maximumMenuBits P fee
    ratDenBits entry.observation ≤ scale ∧ ratDenBits entry.repairs ≤ scale ∧
      ratDenBits entry.failure ≤ scale ∧
      ratDenBits (entry.objective fee penalty) ≤ scale+ratDenBits penalty := by
  let D := P.menuCommonDenominator fee
  let entry := menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty tools stages) row column
  have positive : 0 < D := menuCommonDenominator_pos P fee
  have fields : EntryDen (D^row) entry := cachedSolveMenuTable_entryDen P fee penalty tools stages row column inside
  have denominatorBits := menuCommonDenominator_bits P fee (maximumMenuBits P fee) (maximumMenuBits_bound P fee)
  have powerBits : natBits (D^(row+1)) ≤ (row+1)*(2*(P.certificate.M+1)+2)*maximumMenuBits P fee := by
    have power := natBits_pow_le_of_pos D (row+1) (by omega)
    have product := Nat.mul_le_mul_left (row+1) denominatorBits
    exact power.trans (by simpa only [D,Nat.mul_assoc] using product)
  have inclusion : D^row ∣ D^(row+1) := pow_dvd_pow D (by omega)
  have observation := (ratDenBits_le_of_dvd (pow_pos positive _) (fields.1.trans inclusion)).trans powerBits
  have repairs := (ratDenBits_le_of_dvd (pow_pos positive _) (fields.2.1.trans inclusion)).trans powerBits
  have failure := (ratDenBits_le_of_dvd (pow_pos positive _) (fields.2.2.trans inclusion)).trans powerBits
  have objectiveDen := menu_objective_den_dvd P fee penalty row entry fields
  have objective := ratDenBits_le_of_dvd (Nat.mul_pos (pow_pos positive _) penalty.den_pos) objectiveDen
  have multiply := natBits_mul_le (D^(row+1)) penalty.den
  exact ⟨observation,repairs,failure,objective.trans (multiply.trans (Nat.add_le_add_right powerBits _))⟩

end PDCompute.Solver
