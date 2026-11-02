module
public import Structure.PA17_TM_RatArithmetic_Sub_016e

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016

private theorem payload_length (n : Nat) : (PSTRTMNatValue017.rawPayload n).length = natBits n := by
  simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]

theorem native_length_le (a b : Nat) :
    (nativeTrace a b).length ≤ 4096*(natBits a+natBits b+1)^2 := by
  have hr :
      (PSTRTMRawPack045.rawPackTrace (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)).length ≤
        2048*(natBits a+natBits b+1)^2 := by
    simpa only [payload_length] using
      PSTRTMRawPack045.rawPack_length_le (PSTRTMNatValue017.rawPayload a) (PSTRTMNatValue017.rawPayload b)
  have hp := pairs_length_le a b
  have hb := branchTrace_quadratic (pairs a b)
  have hc := isolatedOutput_length_le (saturatedPairs (pairs a b))
  rw [saturatedPairs_length] at hc
  have hsq := Nat.pow_le_pow_left (show (pairs a b).length+1 ≤ natBits a+natBits b+1 by omega) 2
  have hbm := (Nat.mul_le_mul_left 64 hsq)
  have hcm := (Nat.mul_le_mul_left 256 hsq)
  simp only [nativeTrace,decodedTrace,List.length_append,List.length_map]
  omega

theorem native_visitedSpace_le (a b : Nat) :
    visitedSpace nativeSubMachine (encodeNat a++encodeNat b).length (nativeTrace a b) ≤
      16384*(natBits a+natBits b+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le nativeSubMachine (encodeNat a++encodeNat b).length (nativeTrace a b)
  have ht := native_length_le a b
  simp only [List.length_append,PSTRTMLength004.encodeNat_length] at hs ⊢
  have ha : 0 < natBits a := by simp [natBits]
  have hb : 0 < natBits b := by simp [natBits]
  nlinarith

/-- Original standalone saturating natural subtraction: one fixed597-label
ordinary Bool TM0 and positive polynomial constants precede ALL a,b. No
non-underflow, width, fuel, answer, padding or room qualification is imposed. -/
theorem encodeNat_sub_computes (a b : Nat) :
    computes nativeSubMachine (encodeNat a++encodeNat b) (encodeNat (a-b))
      (4096*(natBits a+natBits b+1)^2) (16384*(natBits a+natBits b+1)^2) := by
  refine ⟨nativeTrace a b,nativeFinal a b,native_runs a b,?_,native_length_le a b,native_visitedSpace_le a b⟩
  rw [native_final_tape]
  exact Turing.Tape.mk'_right₀ _ _

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSub016
