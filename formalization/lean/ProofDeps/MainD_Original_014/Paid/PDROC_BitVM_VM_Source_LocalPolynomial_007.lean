module

public import Paid.PDROC_BitVM_Kernel_RatCompareBudget_059

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.VM.Source

open scoped BigOperators

/-- Uniformize local macro bounds over a fixed finite source program.
This is only finite-code bookkeeping; original input-size conversion
remains the frozen Root096 bridge, not a new paper assumption. -/
theorem finite_local_polynomial {I : Type*} [Fintype I]
    (coefficient degree : I → ℕ) :
    ∃ C D : ℕ, 0 < C ∧ 0 < D ∧
      ∀ index size, coefficient index*(size+1)^degree index ≤ C*(size+1)^D := by
  let C := (∑ index,coefficient index)+1
  let D := (∑ index,degree index)+1
  refine ⟨C,D,by dsimp only [C];omega,by dsimp only [D];omega,?_⟩
  intro index size
  have coeffSum : coefficient index ≤ ∑ item,coefficient item :=
    Finset.single_le_sum (fun item _ => Nat.zero_le (coefficient item)) (Finset.mem_univ index)
  have degreeSum : degree index ≤ ∑ item,degree item :=
    Finset.single_le_sum (fun item _ => Nat.zero_le (degree item)) (Finset.mem_univ index)
  have coeffBound : coefficient index ≤ C := by dsimp only [C];omega
  have degreeBound : degree index ≤ D := by dsimp only [D];omega
  exact Nat.mul_le_mul coeffBound (Nat.pow_le_pow_right (by omega : 1 ≤ size+1) degreeBound)

/-- A single common actual entry-size bound can be substituted into
every chosen macro. No runtime degree, size, padding or fuel is added. -/
theorem finite_local_polynomial_compose {I : Type*} [Fintype I]
    (coefficient degree : I → ℕ) :
    ∃ C D : ℕ, 0 < C ∧ 0 < D ∧
      ∀ index localSize envelope, localSize ≤ envelope →
        coefficient index*(localSize+1)^degree index ≤ C*(envelope+1)^D := by
  obtain ⟨C,D,positiveC,positiveD,uniform⟩ := finite_local_polynomial coefficient degree
  refine ⟨C,D,positiveC,positiveD,?_⟩
  intro index localSize envelope bounded
  exact (uniform index localSize).trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega : localSize+1 ≤ envelope+1) D))

end PDROC.BitVM.VM.Source
