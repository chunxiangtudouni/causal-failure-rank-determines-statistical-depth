module

public import PaperProofs.Paid.PDROC_DataBits_002
public import Mathlib.Algebra.Order.BigOperators.Group.List

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem natBits_pow_le_of_pos (m n : ℕ) (hn : 0 < n) :
    natBits (m ^ n) ≤ n * natBits m := by
  apply natBits_le_of_lt_pow
  · rw [mul_comm n, pow_mul]
    exact Nat.pow_lt_pow_left (natBits_lt_pow m) (by omega)
  · exact Nat.mul_pos hn (natBits_pos m)

theorem menuScalars_length (P : Parameters) (fee : ℚ) :
    (P.menuScalars fee).length = 2 * (P.certificate.M + 1) + 2 := by
  have hf (values : List EndpointConstant) :
      (values.flatMap (fun endpoint => [endpoint.error, endpoint.charge])).length = 2 * values.length := by
    induction values with
    | nil => simp
    | cons first rest ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil, List.length_cons, ih]; omega
  simp only [menuScalars, List.length_append, hf, endpointCache, Array.toList_ofFn,
    List.length_ofFn, List.length_cons, List.length_nil]

theorem menuCommonDenominator_bits (P : Parameters) (fee : ℚ) (L : ℕ)
    (hL : P.MenuEncodingBound fee L) :
    natBits (P.menuCommonDenominator fee) ≤ (2 * (P.certificate.M + 1) + 2) * L := by
  have hne : (P.menuScalars fee).map Rat.den ≠ [] := by
    have hl := menuScalars_length P fee
    intro he
    have := congrArg List.length he
    simp only [List.length_map, List.length_nil] at this
    omega
  have hp := natBits_prod_le ((P.menuScalars fee).map Rat.den) hne
  have hs : (((P.menuScalars fee).map Rat.den).map natBits).sum ≤
      (((P.menuScalars fee).map Rat.den).map natBits).length * L := by
    apply List.sum_le_length_nsmul
    intro d hd
    obtain ⟨den, hden, rfl⟩ := List.mem_map.mp hd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hden
    have hqL := hL.2 q hq
    unfold ratEncodingBits ratDenBits at hqL
    omega
  simpa only [menuCommonDenominator, List.length_map, menuScalars_length] using hp.trans hs

theorem rat_numAbs_le_ceil_abs_mul_den (q : ℚ) : q.num.natAbs ≤ (⌈|q|⌉₊ + 1) * q.den := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have he : (q.num : ℚ) = q * q.den := (div_eq_iff hd.ne').mp (Rat.num_div_den q)
  have heabs : (q.num.natAbs : ℚ) = |q| * q.den := by
    rw [Nat.cast_natAbs, Int.cast_abs, he, abs_mul, abs_of_pos hd]
  have hc : |q| ≤ (⌈|q|⌉₊ : ℚ) := Nat.le_ceil _
  have hx : (q.num.natAbs : ℚ) ≤ ((⌈|q|⌉₊ + 1 : ℕ) : ℚ) * q.den := by
    rw [heabs]
    push_cast
    nlinarith
  exact_mod_cast hx

theorem ratNumBits_le_denBits_ceil_abs (q : ℚ) :
    ratNumBits q ≤ ratDenBits q + natBits (⌈|q|⌉₊ + 1) := by
  have h := (natBits_mono (rat_numAbs_le_ceil_abs_mul_den q)).trans
    (natBits_mul_le (⌈|q|⌉₊ + 1) q.den)
  simpa only [ratNumBits, ratDenBits, Nat.add_comm] using h

theorem menuBitClaims (P : Parameters) : P.MenuBitClaims := by
  intro fee penalty L hL
  have hD := menuCommonDenominator_bits P fee L hL
  refine ⟨hD, ?_⟩
  intro n hn k _hk
  let entry := menuEntryAt
    (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages) n k
  let D := P.menuCommonDenominator fee
  let A := 2 * (P.certificate.M + 1) + 2
  have he : EntryDen (D^n) entry := cachedSolveMenuTable_entryDen P fee penalty P.tools
    P.certificate.stages n k hn
  have hobj := menu_objective_den_dvd P fee penalty n entry he
  have hDpos := menuCommonDenominator_pos P fee
  have hpowpos : 0 < D^(n+1) := pow_pos hDpos _
  have hpower : natBits (D^(n+1)) ≤ (n+1) * A * L := by
    calc
      _ ≤ (n+1) * natBits D := natBits_pow_le_of_pos D (n+1) (by omega)
      _ ≤ (n+1) * (A*L) := Nat.mul_le_mul_left (n+1) hD
      _ = _ := by ring
  have hdiv : D^n ∣ D^(n+1) := pow_dvd_pow D (by omega)
  have ho := (ratDenBits_le_of_dvd hpowpos (he.1.trans hdiv)).trans hpower
  have hr := (ratDenBits_le_of_dvd hpowpos (he.2.1.trans hdiv)).trans hpower
  have hf := (ratDenBits_le_of_dvd hpowpos (he.2.2.trans hdiv)).trans hpower
  have hobjbits : ratDenBits (entry.objective fee penalty) ≤
      (n+1)*A*L + ratDenBits penalty := by
    calc
      _ ≤ natBits (D^(n+1)*penalty.den) :=
        ratDenBits_le_of_dvd (Nat.mul_pos hpowpos penalty.den_pos) hobj
      _ ≤ natBits (D^(n+1)) + ratDenBits penalty := natBits_mul_le _ _
      _ ≤ _ := Nat.add_le_add_right hpower _
  refine ⟨he.1, he.2.1, he.2.2, hobj, ho, hr, hf, hobjbits, ?_⟩
  intro scalar _hscalar
  have hb := ratNumBits_le_denBits_ceil_abs scalar
  omega

end PDROC.DataBits
