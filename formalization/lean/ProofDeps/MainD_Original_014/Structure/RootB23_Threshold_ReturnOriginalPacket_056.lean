module
public import Structure.RootB23_Threshold_ReturnFinalPacket_055
public import Structure.RootB23_Threshold_ReturnOriginalActual_035
public import Structure.RootB23_Threshold_FinalSemantics_Width_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnOriginalPacket
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PaperProofs.Statistics
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002

def badValue (risk : Rat) (depth : ℕ) : Rat := min (1/4) ((FactorSource.factorValue risk depth : Rat)*risk)

def base (risk : Rat) (depth left : ℕ) : List Bool :=
  ReturnRoute.nearLeft (ReturnFarActual.branch risk depth risk) (ReturnFarActual.product risk depth risk) left
    (ReturnBank.archive (ReturnTraverse.base (false::ReturnBank.bArchive risk depth) (FactorSource.bDigits risk depth))
      (FactorSource.factorValue risk depth : Rat) risk)

def archive (risk : Rat) (depth left : ℕ) : List Bool :=
  ReturnFinalPacket.archive (base risk depth left) (badValue risk depth) (controllerB risk depth)

def finalTape (risk : Rat) (depth left : ℕ) : Tape Bool :=
  Tape.mk₂ (archive risk depth left) (thresholdOutput risk depth++List.replicate 16 false)

def tailCap : ℕ := 1231+ReturnFinalPacket.cap+1
def tailCode : Machine tailCap := PSTRTMSeq005.seqMachine ReturnNineSource.code ReturnFinalPacket.code
def tailPort : Fin (tailCap+1) := PSTRTMSeq005.rightLabel (a:=1231) ReturnFinalPacket.finalPort

def cap : ℕ := ReturnOriginal.cap+tailCap+1
def code : Machine cap := PSTRTMSeq005.seqMachine ReturnOriginal.code tailCode
def finalPort : Fin (cap+1) := PSTRTMSeq005.rightLabel (a:=ReturnOriginal.cap) tailPort

def tailCoefficient : ℕ := 1048576*36+(1048576+32768)*128^2
def timeCoefficient : ℕ := ReturnOriginal.timeCoefficient+tailCoefficient
def spaceCoefficient : ℕ := 2*timeCoefficient+2

theorem branch_value (q : Rat) : ReturnRoute.result (decide ((1/4 : Rat)≤q)) q=min (1/4) q := by
  by_cases capped : (1/4 : Rat)≤q
  · simp only [capped,decide_true,ReturnRoute.result,min_eq_left capped]
  · simp only [capped,decide_false,ReturnRoute.result,min_eq_right (le_of_not_ge capped)]

theorem archive_shape (risk : Rat) (depth left : ℕ) :
    ReturnReady.archive risk depth risk left=true::false::ratLeft (base risk depth left) (badValue risk depth) := by
  unfold ReturnReady.archive ReturnRoute.finish
  rw [show ReturnRoute.result (ReturnFarActual.branch risk depth risk) (ReturnFarActual.product risk depth risk)=
    badValue risk depth by exact branch_value _]
  rfl

theorem bad_nonnegative (risk : Rat) (depth : ℕ) (positive : 0<risk) : 0≤badValue risk depth :=
  le_min (by norm_num) (le_of_lt (OriginalBridge.product_positive risk depth positive))

theorem output_exact (risk : Rat) (depth : ℕ) : ReturnFinalPacket.output (badValue risk depth) (controllerB risk depth)=
    thresholdOutput risk depth := by
  have target : OutputArithmetic.Target.value (controllerB risk depth)=controllerTarget risk depth :=
    (PSTRTMThresholdDenominatorRaw202.target_denominator_identity risk depth).symm
  have odds : ReturnNineSource.odds (controllerB risk depth)=(1-controllerTarget risk depth)/controllerTarget risk depth :=
    (PSTRTMThresholdOddsFields211.controller_odds_identity risk depth).symm
  have inverse : ReturnNineSource.inverse (controllerB risk depth)=controllerTarget risk depth/(1-controllerTarget risk depth) :=
    (PSTRTMThresholdOddsFields211.controller_inverse_odds_identity risk depth).symm
  unfold ReturnFinalPacket.output badValue
  rw [target,FinalSemantics.badRisk_identity,odds,inverse]
  rfl

theorem source_tape (risk : Rat) (depth left : ℕ) (positive : 0<risk) :
    ReturnNineSource.finalTape (List.replicate 9 false++ReturnReady.archive risk depth risk left) (controllerB risk depth)=
      Tape.mk₂ (ReturnNineLayout.footerLeft (base risk depth left) (ReturnFinalPacket.fields (badValue risk depth) (controllerB risk depth))) [false] := by
  have actual:=ReturnNineLayout.rawLeft_exact (base risk depth left) (badValue risk depth)
    (bad_nonnegative risk depth positive) (controllerB risk depth)
  rw [←archive_shape] at actual
  exact congrArg (fun west=>Tape.mk₂ west [false]) actual

def tailFee (risk : Rat) (depth : ℕ) : ℕ :=
  1048576*(natBits (controllerB risk depth)+1)^2+
    (1048576+32768)*(ReturnFinalPacket.width (badValue risk depth) (controllerB risk depth)+1)^2

/-- Actual original B/target endpoint -> same-tape arithmetic source ->
observed nine-copy -> real full count5 output. Every old branch archive
is retained in WEST; no all-blank WEST assertion is used. -/
theorem tail_bounded (risk : Rat) (depth left : ℕ) (positive : 0<risk) :
    BoundedRun tailCode (ReturnPairReady.finalTape risk depth risk left) tailPort
      (finalTape risk depth left) (tailFee risk depth) := by
  have source:=ReturnNineSource.actual_bounded risk depth risk left
  rw [source_tape risk depth left positive] at source
  have copied:=ReturnFinalPacket.bounded (base risk depth left) (badValue risk depth) (controllerB risk depth)
    (bad_nonnegative risk depth positive)
  have actual:=source.seq copied
  rw [output_exact] at actual
  exact actual

theorem tail_fee_le (risk : Rat) (depth : ℕ) (hr : 0<risk) (hd : 1≤depth) :
    tailFee risk depth≤tailCoefficient*OriginalBridge.scale risk depth^10 := by
  let s:=OriginalBridge.scale risk depth
  have hs:=OriginalBridge.scale_positive risk depth
  have bWidth:=OriginalBridge.original_b_width risk depth hr hd
  have plus : natBits (controllerB risk depth)+1≤6*s := by
    simp only [FactorSource.bDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn] at bWidth
    dsimp only [s]
    omega
  have widthBound : ReturnFinalPacket.width (badValue risk depth) (controllerB risk depth)+1≤128*s :=
    FinalSemantics.actual_payload_width_le risk depth hr hd
  have power : s^2≤s^10 := Nat.pow_le_pow_right hs (by decide : 2≤10)
  have firstSquare : (natBits (controllerB risk depth)+1)^2≤36*s^10 := by
    have squared:=Nat.pow_le_pow_left plus 2
    simp only [Nat.mul_pow] at squared
    exact squared.trans (Nat.mul_le_mul_left 36 power)
  have secondSquare : (ReturnFinalPacket.width (badValue risk depth) (controllerB risk depth)+1)^2≤128^2*s^10 := by
    have squared:=Nat.pow_le_pow_left widthBound 2
    simp only [Nat.mul_pow] at squared
    exact squared.trans (Nat.mul_le_mul_left (128^2) power)
  have first:=Nat.mul_le_mul_left 1048576 firstSquare
  have second:=Nat.mul_le_mul_left (1048576+32768) secondSquare
  have total:=Nat.add_le_add first second
  simpa only [tailFee,tailCoefficient,Nat.mul_assoc,Nat.add_mul,s] using total

end RootB23.Threshold.ReturnOriginalPacket
