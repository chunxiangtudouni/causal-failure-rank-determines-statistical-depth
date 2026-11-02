module

public import Paid.PDLower_CalibrationCompute_WeightBits_109
public import Paid.PDLower_CalibrationCompute_WeightBranchBits_097
public import Paid.PDLower_CalibrationCompute_RowBitBudget_102
public import Paid.PDLower_CalibrationCompute_CacheLookup_038
public import Paid.PDLower_CalibrationCompute_CalibrationValue_039

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

/-- Entire original weight phase. The real initial caller establishes
all new natural/rational/PC bounds; the actual endpoint cache supplies
the loaded scalar, and the actual denominator selects legal division or
zero. No supplied weight, successful phase or performance claim is used. -/
theorem weightPhase_caller_bits (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma m : ℕ)
    (input : List Cell) (initialCaller before : State) (header : Header)
    (arguments : CallArguments P base endpoints returnPC initialCaller) (initialSafe : SafeBits initialCaller callerBudget)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma)
    (position : before.pc=labelAddress origin .weight) (represented : header.At before base)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before (calleeOperandBudget P origin callerBudget Lgamma))
    (cache : HeapList before header.endpoints (encodeList encodeEndpoint P.endpointCache.toList))
    (endpointBase : header.endpoints=endpoints) (level : header.level=m+1) (bounded : m<P.certificate.M+1)
    (qActual : header.q=P.cachedCappedError m) :
    ∃ after : State,BitSegment origin input before after 400 (calleeOperandBudget P origin callerBudget Lgamma) ∧
      after.pc=labelAddress origin .emit ∧ header.At after base ∧ after.register .fresh=.natural base ∧
      after.register .value=.rational (computedWeight (P.endpointConstant m).error header.q) ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  let budget := calleeOperandBudget P origin callerBudget Lgamma
  let error := (P.endpointConstant m).error
  have control := calleeOperandBudget_control P origin base endpoints returnPC callerBudget Lgamma initialCaller arguments initialSafe
  have endpointsWord := represented.lookup (offset:=1) (value:=.natural header.endpoints) rfl
  have levelWord := represented.lookup (offset:=5) (value:=.natural header.level) rfl
  have qWord := represented.lookup (offset:=11) (value:=.rational header.q) rfl
  have positive : 0<header.level := by omega
  have levelBound : header.level≤P.certificate.M+1 := by omega
  have actualError := endpointHeap_error cache positive levelBound
  have errorCell : before.heap (header.endpoints+(header.level*2-1))=.rational error := by
    simpa [level,error] using actualError.2
  have twiceBound : header.level*2≤calleeNaturalCap base endpoints returnPC P.certificate.M P.certificate.Q := by
    unfold calleeNaturalCap
    omega
  have offsetBound : header.level*2-1≤calleeNaturalCap base endpoints returnPC P.certificate.M P.certificate.Q := by omega
  have addressBound : header.endpoints+(header.level*2-1)≤calleeNaturalCap base endpoints returnPC P.certificate.M P.certificate.Q := by
    rw [endpointBase]
    unfold calleeNaturalCap
    omega
  have twiceBits := calleeOperandBudget_natural P origin base endpoints returnPC callerBudget Lgamma (header.level*2)
    initialCaller arguments initialSafe twiceBound
  have offsetBits := calleeOperandBudget_natural P origin base endpoints returnPC callerBudget Lgamma (header.level*2-1)
    initialCaller arguments initialSafe offsetBound
  have addressBits := calleeOperandBudget_natural P origin base endpoints returnPC callerBudget Lgamma (header.endpoints+(header.level*2-1))
    initialCaller arguments initialSafe addressBound
  have intrinsic := weightPhase_scalar_encodingBits P Lgamma m gammaBits (by omega)
  have numeratorBits : (Cell.rational (1/2-error)).bits≤budget :=
    calleeOperandBudget_rational P origin callerBudget Lgamma _ intrinsic.1
  have denominatorBits : (Cell.rational (1/2-header.q)).bits≤budget := by
    simpa only [qActual] using calleeOperandBudget_rational P origin callerBudget Lgamma _ intrinsic.2.1
  have weightBits : (Cell.rational (computedWeight error header.q)).bits≤budget := by
    simpa only [qActual] using calleeOperandBudget_rational P origin callerBudget Lgamma _ intrinsic.2.2
  have halfEncoding : ratEncodingBits (1/2 : ℚ)=4 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have scalePositive : 0<(P.certificate.Q+1)*(Lgamma+2) := Nat.mul_pos (by omega) (by omega)
  have halfBits : (Cell.rational (1/2)).bits≤budget := by
    apply calleeOperandBudget_rational P origin callerBudget Lgamma (1/2)
    rw [halfEncoding]
    simp only [Nat.mul_assoc]
    omega
  have zeroRat : (Cell.rational 0).bits≤budget := by
    have literal : (Cell.rational 0).bits=4 := by decide
    rw [literal]
    exact control.small
  have zeroNat := ControlBudget.literal P origin base budget 0 control (by decide)
  have oneNat := ControlBudget.literal P origin base budget 1 control (by decide)
  have twoNat := ControlBudget.literal P origin base budget 2 control (by decide)
  have targets : ∀ label,natBits (labelAddress origin label)≤budget := fun label =>
    ControlBudget.pc_target P origin base budget control label
  let middle := weightResult before base header.endpoints header.level error header.q
  have gate := weight_bitSegment origin input before base header.endpoints header.level budget error header.q position safe fresh
    endpointsWord.2 endpointsWord.1 levelWord.2 levelWord.1 qWord.2 qWord.1 actualError.1 errorCell
    (ControlBudget.slot P origin base budget 1 control (by decide)) (ControlBudget.slot P origin base budget 5 control (by decide))
    (ControlBudget.slot P origin base budget 11 control (by decide)) twiceBits offsetBits addressBits zeroNat oneNat twoNat halfBits zeroRat
    numeratorBits denominatorBits (ControlBudget.pc_prefix P origin base budget control before .weight 20 position (by decide)) targets
  by_cases zero : (1/2-header.q : ℚ)=0
  · let branch : State := {middle with pc:=labelAddress origin .zeroWeight}
    let completed := {branch with pc:=branch.pc+1}.set .value (.rational 0)
    let after : State := {completed with pc:=labelAddress origin .emit}
    have first : BitSegment origin input before branch 330 budget := by
      simpa only [middle,branch,ite_eq_left zero] using gate
    have second : BitSegment origin input branch after 45 budget :=
      zeroWeight_bitSegment origin input branch budget rfl first.final zeroRat
        (by simpa only [branch] using calleeOperandBudget_pc P origin callerBudget Lgamma .zeroWeight 1 (by decide)) (targets .emit)
    refine ⟨after,(first.trans second).mono (by decide),rfl,?_,?_,?_,rfl,rfl,rfl⟩
    · exact represented
    · simpa [after,completed,branch,middle,weightResult,weightLoaded,loadSlotResult,State.set] using fresh
    · simp only [after,completed,State.set,Function.update_self,computedWeight,ite_eq_left zero]
  · let branch : State := {middle with pc:=labelAddress origin .divide}
    let completed := divideResult branch (1/2-error) (1/2-header.q)
    let after : State := {completed with pc:=labelAddress origin .emit}
    have first : BitSegment origin input before branch 330 budget := by
      simpa only [middle,branch,ite_eq_right zero] using gate
    have total : branch.register .total=.rational (1/2-error) := by
      simp [branch,middle,weightResult,weightLoaded,loadSlotResult]
    have value : branch.register .value=.rational (1/2-header.q) := by simp [branch,middle,weightResult]
    have quotientBits : (Cell.rational ((1/2-error)/(1/2-header.q))).bits≤budget := by
      simpa only [computedWeight_eq] using weightBits
    have second : BitSegment origin input branch after 45 budget :=
      divide_bitSegment origin input branch (1/2-error) (1/2-header.q) budget rfl first.final total value zero quotientBits
        (by simpa only [branch] using calleeOperandBudget_pc P origin callerBudget Lgamma .divide 1 (by decide)) (targets .emit)
    refine ⟨after,(first.trans second).mono (by decide),rfl,?_,?_,?_,rfl,rfl,rfl⟩
    · exact represented
    · simpa [after,completed,branch,middle,divideResult,weightResult,weightLoaded,loadSlotResult] using fresh
    · simp only [after,completed,divideResult,Function.update_self,computedWeight,ite_eq_right zero,error]

end PDLower.CalibrationCompute
