module

public import Paid.PDLower_CalibrationCompute_ABI_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- Exactly the original calibration operand scale, including the true
endpoint input cells rather than an uncharged derived cache. -/
def calibrationBitScale (P : Parameters) (fee : ℚ) : ℕ :=
  (P.certificate.Q+1)*(ratEncodingBits P.certificate.gamma+2)+maximumMenuBits P fee+1

theorem maximumMenuBits_menuEncodingBound (P : Parameters) (fee : ℚ) :
    P.MenuEncodingBound fee (maximumMenuBits P fee) := by
  have nonempty : ((P.menuScalars fee).map ratEncodingBits)≠[] := by simp [menuScalars]
  constructor
  · unfold maximumMenuBits
    rw [List.foldl_max_eq_max nonempty]
    exact le_max_left _ _
  · intro scalar member
    unfold maximumMenuBits
    rw [List.foldl_max_eq_max nonempty]
    exact (List.le_max_of_mem (List.mem_map.mpr ⟨scalar,member,rfl⟩)).trans (le_max_right _ _)

theorem calibrationBitScale_Q (P : Parameters) (fee : ℚ) : P.certificate.Q+1≤calibrationBitScale P fee := by
  have bound := Nat.mul_le_mul_left (P.certificate.Q+1)
    (by omega : 1≤ratEncodingBits P.certificate.gamma+2)
  simp only [Nat.mul_one] at bound
  unfold calibrationBitScale
  omega

theorem calibrationBitScale_gamma (P : Parameters) (fee : ℚ) :
    ratEncodingBits P.certificate.gamma+2≤calibrationBitScale P fee := by
  have bound := Nat.mul_le_mul_right (ratEncodingBits P.certificate.gamma+2)
    (by omega : 1≤P.certificate.Q+1)
  simp only [Nat.one_mul] at bound
  unfold calibrationBitScale
  omega

/-- Every real readonly calibration-input cell, including endpoint
CHARGES copied by the loader, has the original uniform operand scale. -/
theorem calibrationInput_cell_bits (P : Parameters) (fee : ℚ) (value : Cell)
    (member : value∈calibrationInput P) : value.bits≤4*calibrationBitScale P fee := by
  have qScale := calibrationBitScale_Q P fee
  have gammaScale := calibrationBitScale_gamma P fee
  have menuScale : maximumMenuBits P fee+1≤calibrationBitScale P fee := by
    unfold calibrationBitScale
    omega
  have mQ := PDROC.DataBits.level_le_original_Q P P.certificate.M (le_refl _)
  have mBits : natBits P.certificate.M≤P.certificate.M+1 :=
    Nat.add_le_add_right (Nat.log2_le_self _) 1
  have qBits : natBits P.certificate.Q≤P.certificate.Q+1 :=
    Nat.add_le_add_right (Nat.log2_le_self _) 1
  simp only [calibrationInput,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl|rfl|rfl)|encoded
  · change 1+natBits P.certificate.M≤_
    omega
  · change 1+natBits P.certificate.Q≤_
    omega
  · change 1+ratEncodingBits P.certificate.gamma≤_
    omega
  · simp only [encodeList,List.mem_cons,List.mem_flatMap] at encoded
    rcases encoded with count|⟨endpoint,endpointMember,pair⟩
    · subst value
      have size : P.endpointCache.toList.length=P.certificate.M+1 := by
        simp only [Array.length_toList,endpointCache_size]
      change 1+natBits P.endpointCache.toList.length≤_
      rw [size]
      have bits : natBits (P.certificate.M+1)≤P.certificate.M+1+1 :=
        Nat.add_le_add_right (Nat.log2_le_self _) 1
      omega
    · have bound := maximumMenuBits_menuEncodingBound P fee
      change value∈[Cell.rational endpoint.error,.rational endpoint.charge] at pair
      simp only [List.mem_cons,List.not_mem_nil,or_false] at pair
      rcases pair with rfl|rfl
      · have scalarMember : endpoint.error∈P.menuScalars fee :=
          List.mem_append_left _ (List.mem_flatMap.mpr ⟨endpoint,endpointMember,by simp⟩)
        have bits := bound.2 endpoint.error scalarMember
        change 1+ratEncodingBits endpoint.error≤_
        omega
      · have scalarMember : endpoint.charge∈P.menuScalars fee :=
          List.mem_append_left _ (List.mem_flatMap.mpr ⟨endpoint,endpointMember,by simp⟩)
        have bits := bound.2 endpoint.charge scalarMember
        change 1+ratEncodingBits endpoint.charge≤_
        omega

end PDLower.CalibrationCompute
