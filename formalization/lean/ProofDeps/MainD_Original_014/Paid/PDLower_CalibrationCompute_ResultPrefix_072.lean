module

public import Paid.PDLower_CalibrationCompute_CalibrationValue_039

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- The concrete cache invariant for the original outer induction. The
leading count is emitted by the actual head; each loop appends two cells. -/
def calibrationPrefix (P : Parameters) (count : ℕ) : List Cell :=
  .natural (P.certificate.M+1)::
    (((P.calibrationWeightCache P.endpointCache).toList.take count).flatMap encodeCalibration)

theorem calibrationPrefix_zero (P : Parameters) :
    calibrationPrefix P 0=[.natural (P.certificate.M+1)] := rfl

theorem calibrationPrefix_succ (P : Parameters) (count : ℕ) (inside : count<P.certificate.M+1) :
    calibrationPrefix P (count+1)=calibrationPrefix P count++
      encodeCalibration ((P.calibrationWeightCache P.endpointCache)[count]'(by simpa using inside)) := by
  have bound : count<(P.calibrationWeightCache P.endpointCache).toList.length := by simpa using inside
  simp only [calibrationPrefix,List.take_succ_eq_append_getElem bound,List.flatMap_append,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.cons_append,Array.getElem_toList]

theorem calibrationPrefix_length (P : Parameters) (count : ℕ) (bounded : count≤P.certificate.M+1) :
    (calibrationPrefix P count).length=1+2*count := by
  have length : ((P.calibrationWeightCache P.endpointCache).toList.take count).length=count := by
    rw [List.length_take]
    simp only [Array.length_toList,calibrationWeightCache_size]
    omega
  simp only [calibrationPrefix,List.length_cons,List.length_flatMap,encodeCalibration_length,
    List.map_const',List.sum_replicate,Nat.nsmul_eq_mul,length]
  omega

theorem calibrationPrefix_full (P : Parameters) :
    calibrationPrefix P (P.certificate.M+1)=
      encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList := by
  have length : (P.calibrationWeightCache P.endpointCache).toList.length=P.certificate.M+1 := by simp
  simp only [calibrationPrefix,←length,List.take_length,encodeList]

end PDLower.CalibrationCompute
