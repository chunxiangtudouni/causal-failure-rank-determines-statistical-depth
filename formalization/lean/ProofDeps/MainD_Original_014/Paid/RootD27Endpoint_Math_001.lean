module

public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation

/-- The scalar loop maintains this power by one multiplication per row.
This is a mathematical invariant, never an additional machine opcode. -/
def powerRecurrence (rho : ℚ) : ℕ → ℚ
  | 0 => 1
  | m+1 => powerRecurrence rho m * rho

theorem powerRecurrence_eq (rho : ℚ) (m : ℕ) : powerRecurrence rho m=rho^m := by
  induction m with
  | zero => simp only [powerRecurrence,pow_zero]
  | succ m ih => simp only [powerRecurrence,pow_succ,ih]

def endpointFromPower (gamma fee power : ℚ) (m : ℕ) : Parameters.EndpointConstant :=
  { error:=1/(1+power)
    charge:=fee*((m:ℚ)*(1-2*(1/(1+power)))/(2*gamma)) }

theorem endpointFromPower_original (P : Parameters) (m : ℕ) :
    endpointFromPower P.certificate.gamma P.reviewFee
      (powerRecurrence P.certificate.odds m) m=P.endpointConstant m := by
  rw [powerRecurrence_eq]
  rfl

theorem odds_den_pos (P : Parameters) : 0<1-2*P.certificate.gamma := by
  linarith [P.certificate.gamma_le_quarter]

theorem odds_den_ne_zero (P : Parameters) : 1-2*P.certificate.gamma≠0 :=
  ne_of_gt (odds_den_pos P)

theorem power_pos (P : Parameters) (m : ℕ) :
    0<powerRecurrence P.certificate.odds m := by
  rw [powerRecurrence_eq]
  exact pow_pos P.certificate.odds_pos m

theorem error_den_ne_zero (P : Parameters) (m : ℕ) :
    1+powerRecurrence P.certificate.odds m≠0 := by
  exact ne_of_gt (add_pos zero_lt_one (power_pos P m))

theorem mean_den_ne_zero (P : Parameters) : 2*P.certificate.gamma≠0 := by
  exact ne_of_gt (mul_pos (by norm_num) P.certificate.gamma_pos)

def recurrenceCache (P : Parameters) : Array Parameters.EndpointConstant :=
  Array.ofFn (fun m : Fin (P.certificate.M+1) =>
    endpointFromPower P.certificate.gamma P.reviewFee
      (powerRecurrence P.certificate.odds m.val) m.val)

theorem recurrenceCache_original (P : Parameters) : recurrenceCache P=P.endpointCache := by
  unfold recurrenceCache Parameters.endpointCache
  congr 1
  funext m
  exact endpointFromPower_original P m.val

theorem recurrenceCache_codec_original (P : Parameters) :
    encodeList encodeEndpoint (recurrenceCache P).toList=
      encodeList encodeEndpoint P.endpointCache.toList := by
  rw [recurrenceCache_original]

theorem encodeEndpoint_length (endpoint : Parameters.EndpointConstant) :
    (encodeEndpoint endpoint).length=2 := rfl

theorem encodeEndpoints_length (endpoints : List Parameters.EndpointConstant) :
    (endpoints.flatMap encodeEndpoint).length=2*endpoints.length := by
  induction endpoints with
  | nil => rfl
  | cons endpoint endpoints ih =>
    simp only [List.flatMap_cons,List.length_append,encodeEndpoint_length,
      List.length_cons,ih]
    omega

theorem original_cache_length (P : Parameters) :
    (encodeList encodeEndpoint P.endpointCache.toList).length=2*P.certificate.M+3 := by
  simp only [encodeList,List.length_cons,encodeEndpoints_length,Array.length_toList,
    Parameters.endpointCache_size]
  omega

theorem original_cache_header (P : Parameters) :
    (encodeList encodeEndpoint P.endpointCache.toList).head?=
      some (.natural (P.certificate.M+1)) := by
  simp only [encodeList,List.head?_cons,Array.length_toList,Parameters.endpointCache_size]

end RootD27.Endpoint
