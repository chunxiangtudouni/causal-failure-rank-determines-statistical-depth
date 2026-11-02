module

public import PaperProofs.Paid.PDROC_DataBits_Counts_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid

namespace PDROC.DataBits

theorem certificate_counts_bound (D : CertificateInput) :
    D.t0 + D.M + D.E + D.Q ≤ 128 * (dataInputSize D) ^ 8 := by
  let S := dataInputSize D
  have ht := certificate_t0_bound D
  have hm := certificate_M_bound D
  have he := certificate_E_bound D
  have hq := certificate_Q_bound D
  have hS : 1 ≤ S := Nat.succ_le_of_lt (dataInputSize_pos D)
  have h35 : S ^ 3 ≤ S ^ 5 := pow_le_pow_right₀ hS (by decide : 3 ≤ 5)
  have h45 : S ^ 4 ≤ S ^ 5 := pow_le_pow_right₀ hS (by decide : 4 ≤ 5)
  have h58 : S ^ 5 ≤ S ^ 8 := pow_le_pow_right₀ hS (by decide : 5 ≤ 8)
  nlinarith

theorem certificate_counts_polynomial :
    ∃ C degree : ℕ, 0 < C ∧ ∀ D : CertificateInput,
      D.t0 + D.M + D.E + D.Q ≤ C * (dataInputSize D) ^ degree :=
  ⟨128, 8, by decide, certificate_counts_bound⟩

end PDROC.DataBits
