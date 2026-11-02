module

public import PaperProofs.Paid.PDROC_DataBits_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

structure SolutionGrid (P : Parameters) (fee : ℚ) (D : ℕ) (solution : MultiplierSolve) : Prop where
  table_eq : solution.table = P.cachedSolveMenuTable P.endpointCache fee solution.multiplier
    P.tools P.certificate.stages
  den_dvd : solution.multiplier.den ∣ D
  multiplier_nonneg : 0 ≤ solution.multiplier
  multiplier_le : solution.multiplier ≤ P.Lambda

def StateGrid (P : Parameters) (fee : ℚ) (D : ℕ) : MultiplierState → Prop
  | .exact solution => SolutionGrid P fee D solution
  | .bracket lower upper => SolutionGrid P fee D lower ∧ SolutionGrid P fee D upper

theorem solutionGrid_mono {P : Parameters} {fee : ℚ} {D E : ℕ} {solution : MultiplierSolve}
    (h : SolutionGrid P fee D solution) (hDE : D ∣ E) : SolutionGrid P fee E solution :=
  ⟨h.table_eq, h.den_dvd.trans hDE, h.multiplier_nonneg, h.multiplier_le⟩

theorem stateGrid_mono {P : Parameters} {fee : ℚ} {D E : ℕ} {state : MultiplierState}
    (h : StateGrid P fee D state) (hDE : D ∣ E) : StateGrid P fee E state := by
  cases state with
  | exact solution => exact solutionGrid_mono h hDE
  | bracket lower upper => exact ⟨solutionGrid_mono h.1 hDE, solutionGrid_mono h.2 hDE⟩

theorem midpoint_den_dvd {a b : ℚ} {D : ℕ} (ha : a.den ∣ D) (hb : b.den ∣ D) :
    ((a+b)/2).den ∣ 2*D := by
  have hhalf : ((2:ℚ)⁻¹).den ∣ 2 := by norm_num
  simpa only [div_eq_mul_inv, Nat.mul_comm] using den_mul_common (den_add_common ha hb) hhalf

theorem midpoint_solutionGrid (P : Parameters) (fee : ℚ) (D : ℕ) (lower upper : MultiplierSolve)
    (hl : SolutionGrid P fee D lower) (hu : SolutionGrid P fee D upper) :
    SolutionGrid P fee (2*D)
      (P.cachedSolveMultiplier P.endpointCache fee ((lower.multiplier+upper.multiplier)/2)) := by
  refine ⟨rfl, midpoint_den_dvd hl.den_dvd hu.den_dvd, ?_, ?_⟩
  · change 0 ≤ (lower.multiplier+upper.multiplier)/2
    linarith [hl.multiplier_nonneg, hu.multiplier_nonneg]
  · change (lower.multiplier+upper.multiplier)/2 ≤ P.Lambda
    linarith [hl.multiplier_le, hu.multiplier_le]

theorem cachedBisect_stateGrid (P : Parameters) (fee : ℚ) (D : ℕ) (state : MultiplierState)
    (h : StateGrid P fee D state) : StateGrid P fee (2*D) (P.cachedBisect P.endpointCache fee state) := by
  have hDE : D ∣ 2*D := dvd_mul_left D 2
  cases state with
  | exact solution => exact solutionGrid_mono h hDE
  | bracket lower upper =>
      have hm := midpoint_solutionGrid P fee D lower upper h.1 h.2
      dsimp only [cachedBisect]
      split_ifs
      · exact hm
      · exact ⟨hm, solutionGrid_mono h.2 hDE⟩
      · exact ⟨solutionGrid_mono h.1 hDE, hm⟩

theorem cachedMultiplierStep_stateGrid (P : Parameters) (fee : ℚ) (D : ℕ) (state : MultiplierState)
    (h : StateGrid P fee D state) : StateGrid P fee (2*D) (P.cachedMultiplierStep P.endpointCache fee state) := by
  unfold cachedMultiplierStep
  split_ifs
  · exact stateGrid_mono h (dvd_mul_left D 2)
  · exact cachedBisect_stateGrid P fee D state h

theorem cachedInitialState_grid (P : Parameters) (fee : ℚ) :
    StateGrid P fee P.Lambda.den (P.cachedInitialState P.endpointCache fee) := by
  constructor
  · exact ⟨rfl, by norm_num [cachedSolveMultiplier], by norm_num [cachedSolveMultiplier],
      P.Lambda_pos.le⟩
  · exact ⟨rfl, dvd_refl _, P.Lambda_pos.le, le_refl _⟩

theorem cachedMultiplierSearch_grid (P : Parameters) (fee : ℚ) (steps : ℕ) :
    StateGrid P fee (2^steps*P.Lambda.den) (P.cachedMultiplierSearch P.endpointCache fee steps) := by
  induction steps with
  | zero => simpa only [pow_zero, one_mul, cachedMultiplierSearch] using cachedInitialState_grid P fee
  | succ steps ih =>
      have hs := cachedMultiplierStep_stateGrid P fee (2^steps*P.Lambda.den)
        (P.cachedMultiplierSearch P.endpointCache fee steps) ih
      have he : 2*(2^steps*P.Lambda.den) = 2^(steps+1)*P.Lambda.den := by ring
      rw [he] at hs
      exact hs

def menuTableSizeBound (P : Parameters) (L : ℕ) : ℕ :=
  (P.certificate.stages+1)*(P.tools+1)*menuEntrySizeBound P L

def searchSolutionSizeBound (P : Parameters) (L steps : ℕ) : ℕ :=
  8*(steps+ratEncodingBits P.Lambda+1) + menuTableSizeBound P L

theorem solutionGrid_bits (P : Parameters) (fee : ℚ) (L steps : ℕ)
    (hL : P.MenuEncodingBound fee L) (solution : MultiplierSolve)
    (h : SolutionGrid P fee (2^steps*P.Lambda.den) solution) :
    solveBits solution ≤ searchSolutionSizeBound P L steps := by
  have hpos : 0 < 2^steps*P.Lambda.den := by positivity
  have hd := ratDenBits_le_of_dvd hpos h.den_dvd
  have hm := natBits_mul_le (2^steps) P.Lambda.den
  have htwo : natBits (2^steps) = steps+1 := by simp only [natBits, Nat.log2_two_pow]
  rw [htwo] at hm
  have henc := ratEncodingBits_le_of_range solution.multiplier P.Lambda
    (steps+1+ratDenBits P.Lambda) h.multiplier_nonneg h.multiplier_le (hd.trans hm)
  have hmult : ratEncodingBits solution.multiplier ≤ 8*(steps+ratEncodingBits P.Lambda+1) := by
    unfold ratEncodingBits at henc ⊢
    omega
  have htable := cachedMenuTable_bits_le P fee solution.multiplier L hL
  rw [← h.table_eq] at htable
  exact Nat.add_le_add hmult htable

theorem cachedMultiplierSearch_bits (P : Parameters) (fee : ℚ) (L steps : ℕ)
    (hL : P.MenuEncodingBound fee L) :
    stateBits (P.cachedMultiplierSearch P.endpointCache fee steps) ≤
      1+2*searchSolutionSizeBound P L steps := by
  have h := cachedMultiplierSearch_grid P fee steps
  generalize he : P.cachedMultiplierSearch P.endpointCache fee steps = state at h ⊢
  cases state with
  | exact solution =>
      have hb := solutionGrid_bits P fee L steps hL solution h
      change 1+solveBits solution ≤ _
      omega
  | bracket lower upper =>
      have hl := solutionGrid_bits P fee L steps hL lower h.1
      have hu := solutionGrid_bits P fee L steps hL upper h.2
      change 1+solveBits lower+solveBits upper ≤ _
      omega

end PDROC.DataBits
