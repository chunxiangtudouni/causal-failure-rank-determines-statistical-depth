module

public import PaperProofs.Paid.PDROC_DataBits_003
public import PaperProofs.Paid.PDROC_DataBits_CalibrationFormal_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem natBits_le_succ (n : ℕ) : natBits n ≤ n+1 := by
  simpa only [natBits, Nat.log2_eq_log_two] using Nat.add_le_add_right (Nat.log_le_self 2 n) 1

theorem ratEncodingBits_natCast_menu (n : ℕ) : ratEncodingBits (n : ℚ) = natBits n + 2 := by
  simp only [ratEncodingBits, ratNumBits, ratDenBits, Rat.num_natCast, Rat.den_natCast,
    Int.natAbs_natCast]
  norm_num [natBits]
  omega

theorem rat_abs_le_numAbs (q : ℚ) : |q| ≤ (q.num.natAbs : ℚ) := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hd1 : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have he : (q.num : ℚ) = q*q.den := (div_eq_iff hd.ne').mp (Rat.num_div_den q)
  have heabs : (q.num.natAbs : ℚ) = |q| * q.den := by
    rw [Nat.cast_natAbs, Int.cast_abs, he, abs_mul, abs_of_pos hd]
  have hm := mul_le_mul_of_nonneg_left hd1 (abs_nonneg q)
  nlinarith

theorem rat_ceil_bits_le_numBits (q : ℚ) : natBits (⌈q⌉₊ + 1) ≤ ratNumBits q + 1 := by
  have hceil : ⌈q⌉₊ ≤ q.num.natAbs := Nat.ceil_le.mpr ((le_abs_self q).trans (rat_abs_le_numAbs q))
  have h := (natBits_mono (Nat.add_le_add_right hceil 1)).trans (natBits_add_le q.num.natAbs 1)
  have hone : natBits 1 = 1 := by norm_num [natBits]
  simpa only [ratNumBits, hone] using h

def menuEncodingSize (P : Parameters) (fee : ℚ) : ℕ :=
  512 * (P.certificate.Q+1) * (ratEncodingBits P.certificate.gamma +
    ratEncodingBits P.reviewFee + ratEncodingBits fee + natBits P.certificate.M + 2)

theorem endpointCharge_encodingBits_le (P : Parameters) (fee : ℚ) (m : ℕ)
    (hm : m ≤ P.certificate.M) :
    ratEncodingBits (P.binarySymmetric.endpointCharge m) ≤ menuEncodingSize P fee := by
  let A := ratEncodingBits P.certificate.gamma + ratEncodingBits P.reviewFee +
    ratEncodingBits fee + natBits P.certificate.M + 2
  let T := (P.certificate.Q+1)*A
  have hA : ratEncodingBits P.certificate.gamma + 2 ≤ A := by omega
  have hT : A ≤ T := by dsimp [T]; nlinarith
  have he := calibrationEndpoint_encodingBits_le P (ratEncodingBits P.certificate.gamma) (le_refl _) m hm
  have he' : ratEncodingBits (P.binarySymmetric.endpointError m) ≤ 40*T := by
    exact he.trans (by dsimp [T]; nlinarith)
  have hm' := natBits_mono hm
  have hone : ratEncodingBits (1:ℚ) = 3 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have htwo : ratEncodingBits (2:ℚ) = 4 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hg := ratEncodingBits_mul_le (2:ℚ) P.certificate.gamma
  have hp := ratEncodingBits_mul_le (2:ℚ) (P.binarySymmetric.endpointError m)
  have hd := ratEncodingBits_sub_le (1:ℚ) (2*P.binarySymmetric.endpointError m)
  have hmenc := ratEncodingBits_natCast_menu m
  have hcm := ratEncodingBits_mul_le P.reviewFee (m:ℚ)
  have hdiv := ratEncodingBits_div_le (P.reviewFee*(m:ℚ)) (2*P.certificate.gamma)
  have hprod := ratEncodingBits_mul_le (P.reviewFee*(m:ℚ)/(2*P.certificate.gamma))
    (1-2*P.binarySymmetric.endpointError m)
  rw [hone] at hd
  rw [htwo] at hg hp
  rw [hmenc] at hcm
  rw [PaperProofs.Statistics.BinarySymmetric.Parameters.endpointCharge_formula]
  change ratEncodingBits (P.reviewFee*(m:ℚ)/(2*P.certificate.gamma)*
    (1-2*P.binarySymmetric.endpointError m)) ≤ _
  change _ ≤ 512*(P.certificate.Q+1)*A
  rw [Nat.mul_assoc]
  change _ ≤ 512*T
  dsimp [A] at hT
  have hTpos : 2 ≤ T := by dsimp [T, A]; nlinarith
  omega

theorem menuEncodingSize_bound (P : Parameters) (fee : ℚ) :
    P.MenuEncodingBound fee (menuEncodingSize P fee) := by
  let A := ratEncodingBits P.certificate.gamma + ratEncodingBits P.reviewFee +
    ratEncodingBits fee + natBits P.certificate.M + 2
  have hA : A ≤ menuEncodingSize P fee := by change A ≤ 512*(P.certificate.Q+1)*A; nlinarith
  refine ⟨by dsimp [menuEncodingSize]; nlinarith, ?_⟩
  intro scalar hs
  rcases List.mem_append.mp hs with he | he
  · obtain ⟨endpoint, hendpoint, hscalar⟩ := List.mem_flatMap.mp he
    have hm : ∃ m : Fin (P.certificate.M+1), P.endpointConstant m.val = endpoint := by
      simpa only [endpointCache, Array.toList_ofFn, List.mem_ofFn] using hendpoint
    obtain ⟨m, rfl⟩ := hm
    simp at hscalar
    rcases hscalar with rfl | rfl
    · have hb := calibrationEndpoint_encodingBits_le P (ratEncodingBits P.certificate.gamma)
        (le_refl _) m.val (by omega)
      change ratEncodingBits (P.binarySymmetric.endpointError m.val) ≤ _
      have hscale : ratEncodingBits P.certificate.gamma+2 ≤ A := by omega
      change _ ≤ 512*(P.certificate.Q+1)*A
      nlinarith
    · exact endpointCharge_encodingBits_le P fee m.val (by omega)
  · simp at he
    rcases he with hscalar | hscalar
    · rw [hscalar]
      exact (by dsimp [A]; omega : ratEncodingBits P.reviewFee ≤ A).trans hA
    · rw [hscalar]
      exact (by dsimp [A]; omega : ratEncodingBits fee ≤ A).trans hA

end PDROC.DataBits
