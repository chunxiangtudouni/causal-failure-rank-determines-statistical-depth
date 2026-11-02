module
public import Structure.RootB23_Threshold_ReturnPairReady_037
public import Structure.RootB23_Threshold_OriginalBridge_Bounds_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnResources
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticParse002
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

private theorem linear_square (n : ℕ) : n+1≤(n+1)^2 := by nlinarith only [Nat.zero_le (n^2)]
private theorem fee_coefficient (n : ℕ) : 2*n+5≤64*(n+1)^2 := by nlinarith only [Nat.zero_le (n^2)]
private theorem fee_remaining (n : ℕ) : 4*n^2+45*n+33≤64*(n+1)^2 := by nlinarith only [Nat.zero_le (n^2)]
private theorem grouped_three (a b c p : ℕ) : (a*p+b*(c*p))+p=(a+b*c+1)*p := by ring
private theorem grouped_two (a b c p : ℕ) : a*p+b*(c*p)=(a+b*c)*p := by ring
private theorem degree_ten (a s : ℕ) : 64*((36*s^2)*(a*s^8))=(64*36*a)*s^10 := by
  rw [show 10=2+8 by decide,pow_add]
  ring
private theorem ready_fee_nat (a p n f : ℕ) (first : f≤a*p) (bits : n≤5*p) (unit : 1≤p) :
    f+80*n+192≤(a+600)*p := by nlinarith only [first,bits,unit]

theorem marked_length (q : Rat) : (ReturnRoute.markedNum q).length=natBits q.num.natAbs := by
  have nonempty : ReturnAnchor.numerator q≠[] := PSTRTMThresholdUnitColumnsCost160.rawPayload_ne_nil _
  have positive:=List.length_pos_iff.mpr nonempty
  have original : (ReturnAnchor.numerator q).length=natBits q.num.natAbs := by
    simp only [ReturnAnchor.numerator,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  simp only [ReturnRoute.markedNum,List.length_cons,List.length_tail,original]
  omega

theorem scratch_fee_eq (q : Rat) :
    ReturnRoute.scratchFee q=(PSTRTMThresholdBReblock195.savedLeft q 1).length+28 := by
  rw [ReturnCredit.savedLeft_length]
  simp only [ReturnRoute.scratchFee,marked_length,ReturnAnchor.bDigits,ReturnAnchor.denominator,
    PSTRTMNatValue017.rawPayload,List.length_ofFn]

theorem scratch_fee_le (x y : Rat) (positive : 0<x*y) :
    ReturnRoute.scratchFee (x*y)≤32*fieldWidth x y+540 := by
  have saved:=ReturnCredit.savedLeft_cap_length_le (x*y) positive
  have raw:=PaperProofs.Common.Native.RationalControllerComputation.RootB23.Threshold.Spatial.raw_product_length_le x y
  have packet:=Spatial.MulCap.cap_packet_length (x*y)
  have input:=pair_length x y
  change (encode [.rational x,.rational y]).length=2*fieldWidth x y+14 at input
  change (encode [.rational (x*y)]).length≤2*(encode [.rational x,.rational y]).length at raw
  rw [scratch_fee_eq]
  omega

theorem restore_fee_le (capped : Bool) (x y : Rat) :
    ReturnRoute.restoreFee capped (x*y)≤32768*(fieldWidth x y+1)^2 := by
  cases capped with
  | false=>
    have width:=Spatial.MulCap.product_width_le x y
    change natBits (x*y).num.natAbs+natBits (x*y).den+1≤(encode [.rational x,.rational y]).length at width
    rw [pair_length] at width
    change natBits (x*y).num.natAbs+natBits (x*y).den+1≤2*fieldWidth x y+14 at width
    have bound : natBits (x*y).num.natAbs+natBits (x*y).den+1≤14*(fieldWidth x y+1) := by omega
    have square:=Nat.pow_le_pow_left bound 2
    simp only [Nat.mul_pow] at square
    dsimp only [ReturnRoute.restoreFee,ReturnRoute.result]
    nlinarith only [square]
  | true=>
    have fixed : natBits (1/4 : Rat).num.natAbs+natBits (1/4 : Rat).den+1=5 := by
      have num : (1/4 : Rat).num=1 := by norm_num [div_eq_mul_inv,Rat.num_mul,Rat.num_inv,Rat.den_inv]
      have den : (1/4 : Rat).den=4 := by norm_num [div_eq_mul_inv,Rat.den_mul,Rat.den_inv]
      rw [num,den]
      decide
    have unit : 1≤(fieldWidth x y+1)^2 := by
      simpa only [one_pow] using Nat.pow_le_pow_left (show 1≤fieldWidth x y+1 by omega) 2
    simp only [ReturnRoute.restoreFee,ReturnRoute.result,fixed]
    nlinarith only [unit]

theorem cost_le (capped : Bool) (x y : Rat) (positive : 0<x*y) (left : ℕ) :
    ReturnRoute.cost capped x y (x*y) left≤left+65536*(fieldWidth x y+1)^2 := by
  have scratch:=scratch_fee_le x y positive
  have restore:=restore_fee_le capped x y
  have linear := linear_square (fieldWidth x y)
  dsimp only [ReturnRoute.cost]
  omega

theorem fee_le (capped : Bool) (x y : Rat) (positive : 0<x*y) (left : ℕ) (digits : List Bool) :
    ReturnDestination.fee capped x y (x*y) left digits≤
      64*(digits.length+1)^2*(left+65536*(fieldWidth x y+1)^2+1) := by
  let n:=digits.length
  let c:=ReturnRoute.cost capped x y (x*y) left
  have formula : ReturnDestination.fee capped x y (x*y) left digits=
      (2*n+5)*c+4*n^2+45*n+33 := by
    dsimp only [ReturnDestination.fee,ReturnCopy.copyFee,n,c]
    ring
  have coefficient:=fee_coefficient n
  have remaining:=fee_remaining n
  have scaled:=Nat.mul_le_mul_right c coefficient
  have first : ReturnDestination.fee capped x y (x*y) left digits≤64*(n+1)^2*(c+1) := by
    rw [formula]
    nlinarith only [scaled,remaining]
  exact first.trans (Nat.mul_le_mul_left (64*(n+1)^2) (Nat.add_le_add_right (cost_le capped x y positive left) 1))

def leftCoefficient : ℕ := 2*FixedConsumer.k*16^8
def farCoefficient : ℕ := 64*36*(leftCoefficient+65536*256+1)
def timeCoefficient : ℕ := farCoefficient+600
def pairCoefficient : ℕ := timeCoefficient+8192*36

theorem original_fee (risk : Rat) (depth left right : ℕ) (hr : 0<risk) (hd : 1≤depth)
    (sum : left+right=Producer.left FixedConsumer.k (FactorSource.factorValue risk depth : Rat) risk+
      Spatial.MulCap.window (FactorSource.factorValue risk depth : Rat) risk (32*OriginalBridge.width risk depth+512)) :
    ReturnReady.fee risk depth risk left≤timeCoefficient*OriginalBridge.scale risk depth^10 := by
  let s:=OriginalBridge.scale risk depth
  let w:=OriginalBridge.width risk depth
  let n:=(FactorSource.bDigits risk depth).length
  let c:=leftCoefficient+65536*256+1
  have positive:=OriginalBridge.product_positive risk depth hr
  have hs : 1≤s := OriginalBridge.scale_positive risk depth
  have inputPower : s≤s^10 := by simpa only [pow_one] using Nat.pow_le_pow_right hs (by decide : 1≤10)
  have unit8 : 1≤s^8 := hs.trans (OriginalBridge.original_linear_power risk depth)
  have unit10 : 1≤s^10 := hs.trans inputPower
  have bWidth : n≤5*s := OriginalBridge.original_b_width risk depth hr hd
  have bPlus : n+1≤6*s := by omega
  have bSquare : (n+1)^2≤36*s^2 := by
    simpa only [Nat.mul_pow,show 6^2=36 by decide] using Nat.pow_le_pow_left bPlus 2
  have wSquare : (w+1)^2≤256*s^8 := by
    have square : (w+1)^2≤256*s^2 := by
      simpa only [Nat.mul_pow,show 16^2=256 by decide] using
        Nat.pow_le_pow_left (OriginalBridge.original_width risk depth hr hd) 2
    exact square.trans (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_right hs (by decide : 2≤8)))
  have credit:=OriginalBridge.left_credit_bound (FactorSource.factorValue risk depth : Rat) risk left right sum
  have scaledCredit:=Nat.mul_le_mul_left (2*FixedConsumer.k) (OriginalBridge.original_power risk depth hr hd)
  change left≤2*FixedConsumer.k*(w+1)^8 at credit
  change 2*FixedConsumer.k*(w+1)^8≤2*FixedConsumer.k*(16^8*s^8) at scaledCredit
  have leftBound : left≤leftCoefficient*s^8 := by
    calc
      left≤(2*FixedConsumer.k)*(16^8*s^8) := credit.trans scaledCredit
      _=((2*FixedConsumer.k)*16^8)*s^8 := (Nat.mul_assoc _ _ _).symm
      _=leftCoefficient*s^8 := rfl
  have bracket : left+65536*(w+1)^2+1≤c*s^8 := by
    have combined:=Nat.add_le_add (Nat.add_le_add leftBound (Nat.mul_le_mul_left 65536 wSquare)) unit8
    exact combined.trans_eq (grouped_three leftCoefficient 65536 256 (s^8))
  have fee:=fee_le (ReturnFarActual.branch risk depth risk) (FactorSource.factorValue risk depth : Rat) risk positive
    left (FactorSource.bDigits risk depth)
  have far : ReturnFarActual.fee risk depth risk left≤farCoefficient*s^10 := by
    calc
      ReturnFarActual.fee risk depth risk left≤64*(n+1)^2*(left+65536*(w+1)^2+1) := fee
      _=64*((n+1)^2*(left+65536*(w+1)^2+1)) := Nat.mul_assoc _ _ _
      _≤64*((36*s^2)*(c*s^8)) := by
        exact Nat.mul_le_mul_left 64 (Nat.mul_le_mul bSquare bracket)
      _=farCoefficient*s^10 := degree_ten c s
  unfold ReturnReady.fee timeCoefficient
  change ReturnFarActual.fee risk depth risk left+80*n+192≤(farCoefficient+600)*s^10
  have bits : n≤5*s^10 := bWidth.trans (Nat.mul_le_mul_left 5 inputPower)
  exact ready_fee_nat farCoefficient (s^10) n (ReturnFarActual.fee risk depth risk left) far bits unit10

theorem original_pair_fee (risk : Rat) (depth left right : ℕ) (hr : 0<risk) (hd : 1≤depth)
    (sum : left+right=Producer.left FixedConsumer.k (FactorSource.factorValue risk depth : Rat) risk+
      Spatial.MulCap.window (FactorSource.factorValue risk depth : Rat) risk (32*OriginalBridge.width risk depth+512)) :
    ReturnPairReady.fee risk depth risk left≤pairCoefficient*OriginalBridge.scale risk depth^10 := by
  have first:=original_fee risk depth left right hr hd sum
  have width:=OriginalBridge.original_b_width risk depth hr hd
  have hs:=OriginalBridge.scale_positive risk depth
  have plus : natBits (PaperProofs.Statistics.controllerB risk depth)+1≤6*OriginalBridge.scale risk depth := by
    simp only [FactorSource.bDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn] at width
    omega
  have square : (natBits (PaperProofs.Statistics.controllerB risk depth)+1)^2≤36*OriginalBridge.scale risk depth^10 := by
    have small : (natBits (PaperProofs.Statistics.controllerB risk depth)+1)^2≤36*OriginalBridge.scale risk depth^2 := by
      simpa only [Nat.mul_pow,show 6^2=36 by decide] using Nat.pow_le_pow_left plus 2
    exact small.trans (Nat.mul_le_mul_left 36 (Nat.pow_le_pow_right hs (by decide : 2≤10)))
  have second:=Nat.mul_le_mul_left 8192 square
  exact (Nat.add_le_add first second).trans_eq (grouped_two timeCoefficient 8192 36 (OriginalBridge.scale risk depth^10))

end RootB23.Threshold.ReturnResources
