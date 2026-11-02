module

public import Paid.PDROC_BitVM_VM_Phases_PolynomialOriginal_016
public import Paid.PDROC_BitVM_Size_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.OriginalEnvelope

open PaperProofs.Paid.Computation
open _root_.PDROC.BitVM.VM.Phases.Polynomial

/-- Scalar envelope from the capsule's common C*S^d for the SAME two
actual runs. Includes the real encoded thirteen-field remount length. -/
def envelope (C d S : ℕ) : ℕ := 64 * (C+1) * S^(d+1)

theorem scalar (C d : ℕ) : ScalarBound (envelope C d) :=
  (ScalarBound.constant (64*(C+1))).mul (ScalarBound.identity.power (d+1))

theorem dominate_internal (C d S I Tprep Bprep Tcore Bcore Iprepared : ℕ)
    (positive : 1 ≤ S) (raw : I ≤ 24*S)
    (prepareTime : Tprep ≤ C*S^d) (prepareBits : Bprep ≤ C*S^d)
    (coreTime : Tcore ≤ C*S^d) (coreBits : Bcore ≤ C*S^d)
    (preparedLength : Iprepared ≤ 26*Bprep+10) :
    I ≤ envelope C d S ∧ Tprep ≤ envelope C d S ∧ Bprep ≤ envelope C d S ∧
      Iprepared ≤ envelope C d S ∧ Tcore ≤ envelope C d S ∧ Bcore ≤ envelope C d S := by
  have grow : S^d ≤ S^(d+1) := Nat.pow_le_pow_right positive (by omega)
  have size : S ≤ S^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by omega : 1 ≤ d+1)
  have one : 1 ≤ S^(d+1) := positive.trans size
  have cap : C*S^d ≤ C*S^(d+1) := Nat.mul_le_mul_left C grow
  have common : C*S^d ≤ envelope C d S :=
    cap.trans (Nat.mul_le_mul_right (S^(d+1)) (by omega))
  have actualRaw : I ≤ envelope C d S := by
    have enlarged := raw.trans (Nat.mul_le_mul_left 24 size)
    exact enlarged.trans (Nat.mul_le_mul_right (S^(d+1)) (by omega))
  have remount : Iprepared ≤ envelope C d S := by
    have enlarged := prepareBits.trans cap
    calc
      Iprepared ≤ 26*Bprep+10 := preparedLength
      _ ≤ 26*(C*S^(d+1))+10*S^(d+1) := Nat.add_le_add
        (Nat.mul_le_mul_left 26 enlarged) (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 10 one)
      _ = (26*C+10)*S^(d+1) := by ring
      _ ≤ envelope C d S := Nat.mul_le_mul_right (S^(d+1)) (by omega)
  exact ⟨actualRaw,prepareTime.trans common,prepareBits.trans common,remount,coreTime.trans common,coreBits.trans common⟩

end PDROC.BitVM.VM.Phases.OriginalEnvelope
