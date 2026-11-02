module
public import Structure.PA17_TM_RatArithmetic_SignedSumFields_072a
public import Structure.PA17_TM_RatArithmetic_PairBounds_061a
public import Structure.PA17_TM_RatArithmetic_MulClosure_059a

/-! Only resource metadata for the actual nine-record Add/Sub schedule.
All real code remains043/045/054/055/058/053/044. The record invariants are
proved producer poststates, not qualifications on the original Rat inputs.
No existing five-record theorem is weakened or silently used at count9. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubBounds073

open Turing PA17TMRatArithmeticParse002 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedOuter043
open PA17TMRatArithmeticCachedPair054 PA17TMRatArithmeticPairBounds061
open PA17TMRatArithmeticNativeCache030 PA17TMRatArithmeticWideCache045
open PA17TMRatArithmeticMulFields048 (bank_sum_bounds)
open PA17TMRatArithmeticCachedPass036 PSTRTMLength004
attribute [local implicit_reducible] PA17TMRatArithmeticCachedOuter043.carryCap

def inputPower (x y : Rat) : Nat := ((encode [.rational x,.rational y]).length+1)^4
def timeCoefficient : Nat := 512*feeConstant allocationK
def resourceCoefficient : Nat := 2*timeCoefficient+2

theorem coefficients_pos : 0<timeCoefficient ∧ 0<resourceCoefficient := by
  unfold timeCoefficient resourceCoefficient feeConstant
  constructor <;> positivity

private theorem collected_power (a b c d e w n : Nat) (hw : w≤n) (hn : 1≤n) :
    a*w^4+b*w^3+c*w^2+d*w+e≤(a+b+c+d+e)*n^4 := by
  have h4 := Nat.pow_le_pow_left hw 4
  have h3 := (Nat.pow_le_pow_left hw 3).trans (Nat.pow_le_pow_right hn (by decide : 3≤4))
  have h2 := (Nat.pow_le_pow_left hw 2).trans (Nat.pow_le_pow_right hn (by decide : 2≤4))
  have h1 : w≤n^4 := hw.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hn (by decide : 1≤4))
  have h0 : 1≤n^4 := by simpa only [one_pow] using Nat.pow_le_pow_left hn 4
  have terms := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left a h4) (Nat.mul_le_mul_left b h3))
      (Nat.mul_le_mul_left c h2)) (Nat.mul_le_mul_left d h1)) (Nat.mul_le_mul_left e h0)
  calc
    _ = a*w^4+b*w^3+c*w^2+d*w+e*1 := by ring
    _ ≤ a*n^4+b*n^4+c*n^4+d*n^4+e*n^4 := terms
    _ = _ := by ring

private theorem quadratic_power (a b c w n : Nat) (hw : w≤n) (hn : 1≤n) :
    a*w^2+b*w+c≤(a+b+c)*n^4 := by
  simpa only [Nat.zero_mul,Nat.zero_add] using collected_power 0 0 a b c w n hw hn

private theorem width_le_input (x y : Rat) : fieldWidth x y≤(encode [.rational x,.rational y]).length+1 :=
  (original_width_le_input x y).trans (Nat.le_succ _)

theorem cache_totals9 (x y : Rat) (records : List RecordSpec) (hc : records.length≤9)
    (hg : ∀ r∈records,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈records,r.digits.length≤fieldWidth x y) :
    totalGap records≤18*allocationK*(fieldWidth x y)^2 ∧ totalWidth records≤9*fieldWidth x y := by
  obtain ⟨hgap,hwidth⟩ := bank_sum_bounds records (2*allocationK*(fieldWidth x y)^2) (fieldWidth x y) hg hv
  refine ⟨hgap.trans ?_,hwidth.trans (Nat.mul_le_mul_right _ hc)⟩
  calc
    _ ≤ 9*(2*allocationK*(fieldWidth x y)^2) := Nat.mul_le_mul_right _ hc
    _ = _ := by ring

/-- The same frozen061 base is already large enough for nine old records.
Only its old five-record bridge needed extension; the real kernels did not. -/
theorem produced_bank9_bounds (k width j : Nat) (records : List RecordSpec)
    (hc : records.length≤9) (hj : j≤8)
    (hg : ∀ r∈records,r.gap≤2*k*width^2) (hv : ∀ r∈records,r.digits.length≤width) :
    1≤chargeBase k width ∧ width≤chargeBase k width ∧ j≤chargeBase k width ∧
    k*width^2≤chargeBase k width ∧ totalGap records≤chargeBase k width ∧ totalWidth records≤chargeBase k width := by
  have hp : 1≤(width+1)^2 := Nat.succ_le_of_lt (by positivity : 0<(width+1)^2)
  have hw : width≤(width+1)^2 := by nlinarith
  have low : 64*(width+1)^2≤chargeBase k width := Nat.mul_le_mul_right _ (by omega : 64≤64*(k+1))
  have square := Nat.pow_le_pow_left (show width≤width+1 by omega) 2
  have gap : 18*k*width^2≤chargeBase k width := by
    calc
      _ ≤ 18*k*(width+1)^2 := Nat.mul_le_mul_left _ square
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega : 18*k≤64*(k+1))
  obtain ⟨hgap,hwidth⟩ := bank_sum_bounds records (2*k*width^2) width hg hv
  have hgap9 : totalGap records≤18*k*width^2 := by
    calc
      _ ≤ records.length*(2*k*width^2) := hgap
      _ ≤ 9*(2*k*width^2) := Nat.mul_le_mul_right _ hc
      _ = _ := by ring
  have hwidth9 : totalWidth records≤9*width := hwidth.trans (Nat.mul_le_mul_right _ hc)
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,hgap9.trans gap,by nlinarith⟩

private theorem outer_collected (j k w : Nat) (records : List RecordSpec) :
    outerFee j k records w=(2*totalGap records+4*totalWidth records+21*j)*(w*(w+1)+1)+
      (2*k*w^4+(4*k+4)*w^3+(6*k+86)*w^2+(4*k+212)*w+183) := by
  unfold outerFee prepareFee refillFee loopFee
  ring

private theorem outer_polynomial9 (j k w : Nat) (records : List RecordSpec) (hj : j≤9)
    (hg : totalGap records≤18*k*w^2) (hv : totalWidth records≤9*w) :
    outerFee j k records w≤38*k*w^4+(40*k+40)*w^3+(42*k+311)*w^2+(4*k+437)*w+372 := by
  have bank : 2*totalGap records+4*totalWidth records+21*j≤36*k*w^2+36*w+189 := by
    calc
      _ ≤ 2*(18*k*w^2)+4*(9*w)+21*9 :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 hg) (Nat.mul_le_mul_left 4 hv))
          (Nat.mul_le_mul_left 21 hj)
      _ = _ := by ring
  have scaled := Nat.mul_le_mul_right (w*(w+1)+1) bank
  calc
    _ = (2*totalGap records+4*totalWidth records+21*j)*(w*(w+1)+1)+
        (2*k*w^4+(4*k+4)*w^3+(6*k+86)*w^2+(4*k+212)*w+183) := outer_collected j k w records
    _ ≤ (36*k*w^2+36*w+189)*(w*(w+1)+1)+
        (2*k*w^4+(4*k+4)*w^3+(6*k+86)*w^2+(4*k+212)*w+183) := Nat.add_le_add_right scaled _
    _ = _ := by ring

theorem original_allocation_fee9 (j : Nat) (hj : j≤9) (x y : Rat) (records : List RecordSpec)
    (hc : records.length=j) (hg : ∀ r∈records,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈records,r.digits.length≤fieldWidth x y) :
    outerFee j allocationK records (fieldWidth x y)≤timeCoefficient*inputPower x y := by
  obtain ⟨hgap,hwidth⟩ := cache_totals9 x y records (by rw [hc];exact hj) hg hv
  have fee := outer_polynomial9 j allocationK (fieldWidth x y) records hj hgap hwidth
  have power := collected_power (38*allocationK) (40*allocationK+40) (42*allocationK+311)
    (4*allocationK+437) 372 (fieldWidth x y) ((encode [.rational x,.rational y]).length+1)
    (width_le_input x y) (Nat.succ_le_succ (Nat.zero_le _))
  have coefficient : 38*allocationK+(40*allocationK+40)+(42*allocationK+311)+(4*allocationK+437)+372≤timeCoefficient := by decide
  exact (fee.trans power).trans (Nat.mul_le_mul_right _ coefficient)

private theorem base_cap (x y : Rat) :
    4096*(chargeBase allocationK (fieldWidth x y))^2≤timeCoefficient*inputPower x y :=
  (cap_original_input allocationK x y).trans (Nat.mul_le_mul_right _ (by unfold timeCoefficient;omega))

theorem original_pair_fee9 (j : Nat) (hj : j≤8) (x y : Rat) (fieldA fieldB : PA17TMRatArithmeticFarLoad031.SourceField)
    (memory : Nat) (first : RecordSpec) (records : List RecordSpec) (hc : records.length=j)
    (hg : ∀ r∈first::records,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈first::records,r.digits.length≤fieldWidth x y)
    (nxTail dxTail nyTail dyTail : List Bool)
    (hsource : PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail≤fieldWidth x y)
    (a b : Nat) (ha : natBits a≤fieldWidth x y) (hb : natBits b≤fieldWidth x y) :
    originalPairFee fieldA fieldB memory j first records nxTail dxTail nyTail dyTail
      (allocationK*(fieldWidth x y)^2) a b≤timeCoefficient*inputPower x y := by
  obtain ⟨hone,hw,hjB,hgap,hgB,hvB⟩ := produced_bank9_bounds allocationK (fieldWidth x y) j (first::records)
    (by simp only [List.length_cons,hc];omega) hj hg hv
  have pa : (PA17TMRatArithmeticPairEncode017.payload a).length≤chargeBase allocationK (fieldWidth x y) := by
    rw [PA17TMRatArithmeticPairEncode017.payload_length]
    exact ha.trans hw
  have pb : (PA17TMRatArithmeticPairEncode017.payload b).length≤chargeBase allocationK (fieldWidth x y) := by
    rw [PA17TMRatArithmeticPairEncode017.payload_length]
    exact hb.trans hw
  have bound := original_pair_time_le _ j _ a b hone hjB hgap fieldA fieldB memory first records
    nxTail dxTail nyTail dyTail (hsource.trans hw) hgB hvB pa pb
  exact (original_pair_fee_le fieldA fieldB memory j first records nxTail dxTail nyTail dyTail _ a b).trans
    (bound.trans (base_cap x y))

theorem cached_fees9 (j aLater bLater : Nat) (hj : j≤8) (x y : Rat) (first : RecordSpec)
    (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hc : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (hA : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hB : followingB.length=bLater)
    (hg : ∀ r∈first::records,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈first::records,r.digits.length≤fieldWidth x y)
    (nxTail dxTail nyTail dyTail : List Bool)
    (hsource : PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail≤fieldWidth x y)
    (a b : Nat) (ha : sourceA.digits=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : sourceB.digits=PA17TMRatArithmeticPairEncode017.payload b) :
    cachedPairFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
      nxTail dxTail nyTail dyTail (allocationK*(fieldWidth x y)^2) a b≤timeCoefficient*inputPower x y ∧
    cachedReadyFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
      nxTail dxTail nyTail dyTail (allocationK*(fieldWidth x y)^2)≤timeCoefficient*inputPower x y := by
  obtain ⟨hone,hw,hjB,hgap,hgB,hvB⟩ := produced_bank9_bounds allocationK (fieldWidth x y) j (first::records)
    (by simp only [List.length_cons,hc];omega) hj hg hv
  have neA : sourceA.digits≠[] := by rw [ha];exact PA17TMRatArithmeticFlagZero028.payload_ne_nil a
  have neB : sourceB.digits≠[] := by rw [hb];exact PA17TMRatArithmeticFlagZero028.payload_ne_nil b
  have pa : (PA17TMRatArithmeticPairEncode017.payload a).length≤chargeBase allocationK (fieldWidth x y) := by
    rw [←ha]
    exact (selected_bounds _ j first records beforeA sourceA followingA hc hbankA hgB hvB).2.2.2
  have pb : (PA17TMRatArithmeticPairEncode017.payload b).length≤chargeBase allocationK (fieldWidth x y) := by
    rw [←hb]
    exact (selected_bounds _ j first records beforeB sourceB followingB hc hbankB hgB hvB).2.2.2
  have bound := cached_pair_time_le _ j aLater bLater _ a b hone hjB hgap first records beforeA sourceA followingA
    beforeB sourceB followingB hc hbankA hA hbankB hB neA neB nxTail dxTail nyTail dyTail (hsource.trans hw) hgB hvB pa pb
  have fee := (cached_pair_fee_le j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
    nxTail dxTail nyTail dyTail _ a b).trans (bound.trans (base_cap x y))
  refine ⟨fee,?_⟩
  unfold cachedPairFee at fee
  omega

theorem native_record_fee9 (x y : Rat) (a b : Nat) (hs : scale a b≤4*fieldWidth x y) :
    65536*(scale a b)^2≤timeCoefficient*inputPower x y := by
  have bound := (PA17TMRatArithmeticRatDivFields066.native_budget_le x y a b hs).1
  change 65536*(scale a b)^2≤PA17TMRatArithmeticRatDivFields066.nativeTimeCoefficient*inputPower x y at bound
  have hc : PA17TMRatArithmeticRatDivFields066.nativeTimeCoefficient≤timeCoefficient := by decide
  exact bound.trans (Nat.mul_le_mul_right _ hc)

theorem native_tail_fee9 (j : Nat) (hj : j≤8) (x y : Rat) (first : RecordSpec) (later : List RecordSpec)
    (nx dx ny dy : List Bool) (newGap a b value : Nat)
    (hg : totalGap (first::later)≤18*allocationK*(fieldWidth x y)^2)
    (hv : totalWidth (first::later)≤9*fieldWidth x y) (hn : newGap≤2*allocationK*(fieldWidth x y)^2)
    (hs : scale a b≤4*fieldWidth x y) (hout : natBits value≤fieldWidth x y)
    (hsource : PA17TMRatArithmeticWidth018.bankWidth nx dx ny dy≤fieldWidth x y) :
    PA17TMRatArithmeticNativeTail055.tailFee j first later nx dx ny dy newGap a b value≤timeCoefficient*inputPower x y := by
  have squared := Nat.pow_le_pow_left hs 2
  have fee : PA17TMRatArithmeticNativeTail055.tailFee j first later nx dx ny dy newGap a b value≤
      (1048576+20*allocationK)*(fieldWidth x y)^2+22*fieldWidth x y+157 := by
    unfold PA17TMRatArithmeticNativeTail055.tailFee
    nlinarith only [hg,hv,hn,squared,hout,hsource,hj]
  have power := quadratic_power (1048576+20*allocationK) 22 157 (fieldWidth x y)
    ((encode [.rational x,.rational y]).length+1) (width_le_input x y) (Nat.succ_le_succ (Nat.zero_le _))
  exact (fee.trans power).trans (Nat.mul_le_mul_right _ (by decide : (1048576+20*allocationK)+22+157≤timeCoefficient))

theorem observe_fee9 (sourceLater allLater : Nat) (hs : sourceLater≤2) (hj : allLater≤8)
    (x y : Rat) (first : RecordSpec) (before following : List RecordSpec)
    (nx dx ny dy : List Bool) (sourceGap u : Nat)
    (hg : totalGap (first::PA17TMRatArithmeticZeroCarry058.observedRecords before following sourceGap u)≤18*allocationK*(fieldWidth x y)^2)
    (hv : totalWidth (first::PA17TMRatArithmeticZeroCarry058.observedRecords before following sourceGap u)≤9*fieldWidth x y)
    (hgf : totalGap following≤4*allocationK*(fieldWidth x y)^2) (hvf : totalWidth following≤2*fieldWidth x y)
    (hu : natBits u≤fieldWidth x y) (hsource : PA17TMRatArithmeticWidth018.bankWidth nx dx ny dy≤fieldWidth x y) :
    PA17TMRatArithmeticZeroCarry058.observeFee sourceLater allLater first before following nx dx ny dy sourceGap u≤
      timeCoefficient*inputPower x y := by
  have fee : PA17TMRatArithmeticZeroCarry058.observeFee sourceLater allLater first before following nx dx ny dy sourceGap u≤
      26*allocationK*(fieldWidth x y)^2+32*fieldWidth x y+208 := by
    unfold PA17TMRatArithmeticZeroCarry058.observeFee PA17TMRatArithmeticZeroCarry058.readFee
      PA17TMRatArithmeticZeroCarry058.returnFee
    nlinarith only [hg,hv,hgf,hvf,hu,hsource,hs,hj]
  have power := quadratic_power (26*allocationK) 32 208 (fieldWidth x y)
    ((encode [.rational x,.rational y]).length+1) (width_le_input x y) (Nat.succ_le_succ (Nat.zero_le _))
  exact (fee.trans power).trans (Nat.mul_le_mul_right _ (by decide : 26*allocationK+32+208≤timeCoefficient))

theorem output_fee9 (j : Nat) (hj : j≤8) (x y : Rat) (first : RecordSpec) (later : List RecordSpec)
    (nx dxTail ny dyTail : List Bool) (gap u v : Nat)
    (hg : totalGap (first::later)≤18*allocationK*(fieldWidth x y)^2)
    (hv : totalWidth (first::later)≤9*fieldWidth x y)
    (hsource : PA17TMRatArithmeticFinalClean039.sourceWidth nx dxTail ny dyTail≤fieldWidth x y)
    (hgap : gap≤allocationK*(fieldWidth x y)^2)
    (hu : (PA17TMRatArithmeticPairEncode017.payload u).length≤fieldWidth x y)
    (hden : (PA17TMRatArithmeticPairEncode017.payload v).length≤fieldWidth x y) :
    1+PA17TMRatArithmeticOutputFinish044.outputFee j first later nx dxTail ny dyTail gap u v≤timeCoefficient*inputPower x y := by
  have size : PA17TMRatArithmeticOutputFinish044.pairSize u v≤2*fieldWidth x y+1 := by
    unfold PA17TMRatArithmeticOutputFinish044.pairSize
    omega
  have squared := Nat.pow_le_pow_left size 2
  have fee : 1+PA17TMRatArithmeticOutputFinish044.outputFee j first later nx dxTail ny dyTail gap u v≤
      (74*allocationK+256)*(fieldWidth x y)^2+392*fieldWidth x y+661 := by
    unfold PA17TMRatArithmeticOutputFinish044.outputFee PA17TMRatArithmeticOutputFinish044.tailFee
      PA17TMRatArithmeticFinalClean039.cacheGap PA17TMRatArithmeticFinalClean039.cacheWidth
    nlinarith only [hg,hv,hsource,hgap,squared,hj]
  have power := quadratic_power (74*allocationK+256) 392 661 (fieldWidth x y)
    ((encode [.rational x,.rational y]).length+1) (width_le_input x y) (Nat.succ_le_succ (Nat.zero_le _))
  exact (fee.trans power).trans (Nat.mul_le_mul_right _ (by decide : (74*allocationK+256)+392+661≤timeCoefficient))

/-- Keep EXACTLY the consumer's real witness. This theorem supplies only
the original-input resource rescaling, never an assumed or replacement run. -/
theorem same_actual_trace9 {states : Nat} (machine : Machine states) (x y : Rat)
    (start final : MachineState states) (trace : List (MachineState states))
    (actual : PSTRTMSeq005.RunsFrom machine start trace final) (fee : Nat)
    (ht : trace.length≤fee) (hf : fee≤timeCoefficient*inputPower x y) :
    ∃ sameTrace, sameTrace=trace ∧ PSTRTMSeq005.RunsFrom machine start sameTrace final ∧
      sameTrace.length≤resourceCoefficient*inputPower x y ∧
      ∀ k, visitedSpace machine (encode [.rational x,.rational y]).length (sameTrace.take k)≤resourceCoefficient*inputPower x y := by
  let i := (encode [.rational x,.rational y]).length
  have input : i+1≤(i+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le i)) (by decide : 1≤4)
  have time : trace.length≤timeCoefficient*(i+1)^4 := ht.trans hf
  have hc : timeCoefficient≤resourceCoefficient := by unfold resourceCoefficient;omega
  refine ⟨trace,rfl,actual,time.trans (Nat.mul_le_mul_right _ hc),?_⟩
  intro k
  have space := PSTRTMTrace002.visitedSpace_le machine i (trace.take k)
  have taken : (trace.take k).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  change visitedSpace machine i (trace.take k)≤resourceCoefficient*(i+1)^4
  calc
    _ ≤ i+2*(trace.take k).length+1 := space
    _ ≤ i+2*(timeCoefficient*(i+1)^4)+1 := Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (taken.trans time)) i) 1
    _ = (i+1)+2*(timeCoefficient*(i+1)^4) := by ac_rfl
    _ ≤ (i+1)^4+2*(timeCoefficient*(i+1)^4) := Nat.add_le_add_right input _
    _ = (2*timeCoefficient+1)*(i+1)^4 := by ring
    _ ≤ resourceCoefficient*(i+1)^4 := Nat.mul_le_mul_right _ (by unfold resourceCoefficient;omega)

theorem actual_allocation_contract9 (p j : Nat) (memory : Fin (p+1)) (hj : j≤9)
    (records : List RecordSpec) (hc : records.length=j) (x y : Rat)
    (hg : ∀ r∈records,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈records,r.digits.length≤fieldWidth x y) :
    ∃ trace, PSTRTMSeq005.RunsFrom (carryMachine p j allocationK)
      (carryEntry p j allocationK memory (Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (bankTail records []))))) trace
      (carryFinal p j allocationK memory (Tape.mk₂ [false]
        (prefixRight (sign x) (originalBank x y (cachedTail records (allocationK*(fieldWidth x y)^2)))))) ∧
      trace.length≤resourceCoefficient*inputPower x y ∧
      ∀ k, visitedSpace (carryMachine p j allocationK) (encode [.rational x,.rational y]).length (trace.take k)≤resourceCoefficient*inputPower x y := by
  obtain ⟨trace,actual,time,_space⟩ := original_carry_contract p j allocationK memory records hc x y
  obtain ⟨same,heq,run,length,space⟩ := same_actual_trace9 (states:=PA17TMRatArithmeticCachedOuter043.carryCap p j allocationK)
    (carryMachine p j allocationK) x y _ _ trace actual _ time
    (original_allocation_fee9 j hj x y records hc hg hv)
  exact ⟨same,run,length,space⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubBounds073
