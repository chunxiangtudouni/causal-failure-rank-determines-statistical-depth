module

public import PaperProofs.Paid.PenaltyProgram
public import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace PDMenu

open PaperProofs

theorem endpointError_one (P : Statistics.BinarySymmetric.Parameters) :
    P.endpointError 1 = 1 / 2 - P.gamma := by
  have hd : 1 - 2 * P.gamma ≠ 0 := ne_of_gt (by linarith [P.gamma_le_quarter])
  have ho : 1 + P.odds ≠ 0 := ne_of_gt (by linarith [P.odds_gt_one])
  simp only [Statistics.BinarySymmetric.Parameters.endpointError, pow_one]
  unfold Statistics.BinarySymmetric.Parameters.odds at *
  field_simp
  ring

theorem endpointError_le_one (P : Statistics.BinarySymmetric.Parameters) (m : ℕ) (hm : 1 ≤ m) :
    P.endpointError m ≤ 1 / 2 - P.gamma := by
  rw [← endpointError_one P]
  exact P.endpointError_strictAnti.antitone hm

theorem endpointMeanCount_increment (P : Statistics.BinarySymmetric.Parameters) (m : ℕ) :
    1 ≤ P.endpointMeanCount (m + 1) - P.endpointMeanCount m := by
  have he := P.endpointError_strictAnti.antitone (Nat.le_succ m)
  have he1 := endpointError_le_one P (m + 1) (by omega)
  have hprod := mul_nonneg (Nat.cast_nonneg m : (0 : ℚ) ≤ m)
    (sub_nonneg.mpr he)
  unfold Statistics.BinarySymmetric.Parameters.endpointMeanCount
  rw [← sub_div, le_div_iff₀ (mul_pos (by norm_num) P.gamma_pos)]
  push_cast
  nlinarith

theorem endpointCharge_increment (P : Statistics.BinarySymmetric.Parameters) (m : ℕ) :
    P.reviewFee ≤ P.endpointCharge (m + 1) - P.endpointCharge m := by
  have h := mul_le_mul_of_nonneg_left (endpointMeanCount_increment P m) P.reviewFee_pos.le
  simpa only [mul_one, mul_sub, Statistics.BinarySymmetric.Parameters.endpointCharge] using h

theorem endpointCharge_linear_lower (P : Statistics.BinarySymmetric.Parameters) (m : ℕ) :
    P.reviewFee * m ≤ P.endpointCharge m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := endpointCharge_increment P m
    push_cast
    nlinarith

theorem endpointCharge_tendsto (P : Statistics.BinarySymmetric.Parameters) :
    Tendsto (fun m : ℕ => (P.endpointCharge m : ℝ)) atTop atTop := by
  have hc : (0 : ℝ) < P.reviewFee := by exact_mod_cast P.reviewFee_pos
  have ht : Tendsto (fun m : ℕ => (P.reviewFee : ℝ) * m) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc
  exact tendsto_atTop_mono (fun m => by exact_mod_cast endpointCharge_linear_lower P m) ht

theorem paidEndpointGrowth (P : Paid.Parameters) : P.PaidEndpointGrowth := by
  refine ⟨endpointCharge_tendsto P.binarySymmetric, ?_⟩
  intro m hm
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  change P.binarySymmetric.reviewFee ≤ _
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using endpointCharge_increment P.binarySymmetric a

theorem paidBadSuccessor_le_penalty (P : Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) :
    P.paidBadSuccessor fee hfee n k penalty ≤ penalty := by
  cases k <;> simp only [Paid.Parameters.paidBadSuccessor, le_refl, min_le_left]

theorem paidGoodSuccessor_ne_top (P : Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (hpenalty : penalty ≠ ⊤) :
    P.paidGoodSuccessor fee hfee n k penalty ≠ ⊤ :=
  ne_top_of_le_ne_top hpenalty (P.freshPaidPenalty_le_penalty fee hfee (n - 1) k penalty)

theorem paidBadSuccessor_ne_top (P : Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (hpenalty : penalty ≠ ⊤) :
    P.paidBadSuccessor fee hfee n k penalty ≠ ⊤ :=
  ne_top_of_le_ne_top hpenalty (paidBadSuccessor_le_penalty P fee hfee n k penalty)

theorem paidEndpointObjective_ne_top (P : Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞) (hpenalty : penalty ≠ ⊤) (m : ℕ) :
    P.paidEndpointObjective fee hfee n k penalty m ≠ ⊤ := by
  unfold Paid.Parameters.paidEndpointObjective
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (paidGoodSuccessor_ne_top P fee hfee n k penalty hpenalty)⟩,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (paidBadSuccessor_ne_top P fee hfee n k penalty hpenalty)⟩

theorem paidEndpointMinimumExists (P : Paid.Parameters) : P.PaidEndpointMinimumExists := by
  classical
  intro fee hfee n k penalty _hn hp
  let f := P.paidEndpointObjective fee hfee n k penalty
  have hf0 : f 0 ≠ ⊤ := paidEndpointObjective_ne_top P fee hfee n k penalty hp 0
  obtain ⟨K, hK⟩ := (eventually_atTop.mp ((endpointCharge_tendsto P.binarySymmetric).eventually
    (eventually_gt_atTop ((f 0).toReal))))
  have houtside : ∀ m, K ≤ m → f 0 < f m := by
    intro m hm
    have hcharge : f 0 < ENNReal.ofReal (P.binarySymmetric.endpointCharge m : ℝ) := by
      rw [← ENNReal.ofReal_toReal hf0]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (ENNReal.toReal_nonneg) |>.mpr (hK m hm)
    exact hcharge.trans_le (le_add_right (le_add_right le_rfl))
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Finset.range (K + 1)) f (by simp)
  have hj0 : f j ≤ f 0 := hmin 0 (by simp)
  have hglobal : ∀ m, f j ≤ f m := by
    intro m
    by_cases hm : m < K + 1
    · exact hmin m (Finset.mem_range.mpr hm)
    · exact hj0.trans (houtside m (by omega)).le
  have hex : ∃ m, ∀ i, f m ≤ f i := ⟨j, hglobal⟩
  let m := Nat.find hex
  have hmspec : ∀ i, f m ≤ f i := Nat.find_spec hex
  refine ⟨m, ⟨hmspec, ?_⟩, ?_⟩
  · intro other ho
    exact Nat.find_min' hex ho
  · exact le_antisymm (iInf_le f m) (le_iInf hmspec)

end PDMenu
