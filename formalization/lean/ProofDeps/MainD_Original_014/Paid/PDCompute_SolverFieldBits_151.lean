module

public import Paid.PDCompute_SolverChargeRange_150

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits

theorem solverScalar_le_twoPow (q : ℚ) (L : ℕ) (bounded : ratEncodingBits q ≤ L) :
    q ≤ ((2^L : ℕ) : ℚ) := by
  have numerator : ratNumBits q ≤ L := by unfold ratEncodingBits at bounded; omega
  have natural : q.num.natAbs ≤ 2^L :=
    (natBits_lt_pow q.num.natAbs).le.trans (Nat.pow_le_pow_right (by decide) numerator)
  exact (le_abs_self q).trans ((rat_abs_le_numAbs q).trans (by exact_mod_cast natural))

theorem solverCharge_le_twoPow (P : Parameters) (fee : ℚ) (m : ℕ) (inside : m≤P.certificate.M) :
    P.binarySymmetric.endpointCharge m ≤ ((2^maximumMenuBits P fee : ℕ) : ℚ) := by
  have bound:=(maximumMenuBits_bound P fee).2 _ (endpoint_scalar_mem P fee m inside).2
  exact solverScalar_le_twoPow _ _ bound

def solverFieldMagnitude (L n : ℕ) : ℚ := (n:ℚ)*(((2^L : ℕ):ℚ)+1)+1

theorem solverFieldMagnitude_bits (L n : ℕ) :
    ratEncodingBits (solverFieldMagnitude L n) ≤ 64*(L+natBits n+1) := by
  have power:=natBits_pow_le 2 L
  have two : natBits 2=2 := by norm_num [natBits]
  rw [two] at power
  have cap : ratEncodingBits (((2^L : ℕ):ℚ)) ≤ 2*L+3 := by rw [ratEncodingBits_natCast_menu]; omega
  have one : ratEncodingBits (1:ℚ)=3 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have plus:=ratEncodingBits_add_le (((2^L : ℕ):ℚ)) 1
  have multiply:=ratEncodingBits_mul_le (n:ℚ) ((((2^L : ℕ):ℚ))+1)
  have finish:=ratEncodingBits_add_le ((n:ℚ)*((((2^L : ℕ):ℚ))+1)) 1
  rw [one] at plus finish
  rw [ratEncodingBits_natCast_menu] at multiply
  change ratEncodingBits (solverFieldMagnitude L n) ≤ _ at finish
  omega

/-- Full rational encodings, not denominator bits alone, for every
ORIGINAL arbitrary-n/k table cell. Penalty bits do not enter stored stats. -/
theorem arbitraryTable_fieldBits (P : Parameters) (fee penalty : ℚ) (n k row column : ℕ) (inside : row≤n) :
    let entry:=menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) row column
    let L:=maximumMenuBits P fee
    let bound:=2*((n+1)*(2*(P.certificate.M+1)+2)*L)+64*(L+natBits n+1)+2
    ratEncodingBits entry.observation ≤ bound ∧ ratEncodingBits entry.repairs ≤ bound ∧ ratEncodingBits entry.failure ≤ bound := by
  let L:=maximumMenuBits P fee
  let entry:=menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) row column
  let bound:=(n+1)*(2*(P.certificate.M+1)+2)*L
  let C : ℚ:=((2^L : ℕ):ℚ)
  have Cnonneg : 0 ≤ C := Nat.cast_nonneg _
  have ranges:=solverTable_range P fee penalty C Cnonneg (fun m valid=>solverCharge_le_twoPow P fee m valid) k n row column inside
  have denominators:=arbitraryTable_entry_denBits P fee penalty n k row column inside
  have scale : (row+1)*(2*(P.certificate.M+1)+2)*L ≤ bound :=
    Nat.mul_le_mul_right L (Nat.mul_le_mul_right _ (Nat.add_le_add_right inside 1))
  have observationDen:=denominators.1.trans scale
  have repairsDen:=denominators.2.1.trans scale
  have failureDen:=denominators.2.2.1.trans scale
  have rowCast : (row:ℚ) ≤ n := by exact_mod_cast inside
  have magnitude : entry.observation ≤ solverFieldMagnitude L n ∧ entry.repairs ≤ solverFieldMagnitude L n ∧ entry.failure ≤ solverFieldMagnitude L n := by
    dsimp only [solverFieldMagnitude]
    have nNonneg : (0:ℚ) ≤ n := Nat.cast_nonneg _
    constructor
    · have product:=mul_le_mul_of_nonneg_right rowCast Cnonneg
      nlinarith [ranges.observation_le]
    constructor
    · nlinarith [ranges.repairs_le,mul_nonneg nNonneg Cnonneg]
    · nlinarith [ranges.failure_le,mul_nonneg nNonneg Cnonneg]
  have observation:=ratEncodingBits_le_of_range entry.observation (solverFieldMagnitude L n) bound ranges.observation_nonneg magnitude.1 observationDen
  have repairs:=ratEncodingBits_le_of_range entry.repairs (solverFieldMagnitude L n) bound ranges.repairs_nonneg magnitude.2.1 repairsDen
  have failure:=ratEncodingBits_le_of_range entry.failure (solverFieldMagnitude L n) bound ranges.failure_nonneg magnitude.2.2 failureDen
  have magnitudeBits:=solverFieldMagnitude_bits L n
  change ratEncodingBits entry.observation≤2*bound+64*(L+natBits n+1)+2 ∧
    ratEncodingBits entry.repairs≤2*bound+64*(L+natBits n+1)+2 ∧
    ratEncodingBits entry.failure≤2*bound+64*(L+natBits n+1)+2
  have widened:=Nat.add_le_add_right (Nat.add_le_add_left magnitudeBits (2*bound)) 2
  exact ⟨observation.trans widened,repairs.trans widened,failure.trans widened⟩

end PDCompute.Solver
