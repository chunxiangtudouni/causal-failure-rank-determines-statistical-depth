module
public import Structure.PA17_TM_RatArithmetic_CachedPair_054f
public import Structure.PA17_TM_RatArithmetic_PairInput_050e
public import Structure.PA17_TM_RatArithmetic_MulFields_048c
public import Structure.PA17_TM_RatArithmetic_WideCache_045b

/-! Original-input resource bounds for the multiplication controller's
at-most-five real cache records. All bank conditions describe produced
intermediate tapes, never an extra qualification on original x/y. No code,
copy loop or control dispatcher is introduced. The incoming finite row p
does not enter any coefficient. Root's whole-Mul audit covers this scope. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairBounds061

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticCachedLoad038 PA17TMRatArithmeticCachedPair054
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticPairInput050
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticMulFields048

private theorem linear_square (base : Nat) (hone : 1≤base) : base≤base^2 := by nlinarith

theorem original_row_time_le (base j gap : Nat) (hone : 1≤base) (hj : j≤base) (hgap : gap≤base)
    (field : SourceField) (kind : Destination) (first : RecordSpec) (records : List RecordSpec)
    (nxTail dxTail nyTail dyTail a : List Bool)
    (hw : PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail≤base)
    (hg : totalGap (first::records)≤base) (hv : totalWidth (first::records)≤base) (ha : a.length≤base) :
    originalBankRowTime field kind j gap first records nxTail dxTail nyTail dyTail a≤512*base^2 := by
  let m := (false::sourceTail field nxTail dxTail nyTail dyTail).length
  let cost := sourceCost field dxTail nyTail dyTail
  let far := originalFarCost cost j first records
  let nav := navigationFee nxTail dxTail nyTail
  have hm : m≤base := (source_length_le_width field nxTail dxTail nyTail dyTail).trans hw
  have hc : cost≤25*base := by have h := source_cost_le_width field nxTail dxTail nyTail dyTail; omega
  have hn : nav≤19*base := by have h := navigation_fee_le_width nxTail dxTail nyTail dyTail; omega
  have hf : far≤55*base := by unfold far originalFarCost; omega
  have hd : destinationFee kind a.length gap≤10*base := by cases kind <;> simp only [destinationFee] <;> omega
  have hs := Nat.pow_le_pow_left hm 2
  have hp := Nat.mul_le_mul (show 2*far+2*gap+4*a.length+51≤167*base by omega) hm
  have hl : 2*far+2*gap+4*a.length+33+
      (cost+totalGap (first::records)+2*totalWidth (first::records)+9*(j+1)+3+
        destinationFee kind a.length gap)+nav+2≤229*base := by omega
  have hb := linear_square base hone
  change nav+((4*m^2+(2*far+2*gap+4*a.length+51)*m+2*far+2*gap+4*a.length+33)+
    (cost+totalGap (first::records)+2*totalWidth (first::records)+9*(j+1)+3+
      destinationFee kind a.length gap))+2≤512*base^2
  nlinarith

theorem home_time_le (base j gap : Nat) (hone : 1≤base) (hj : j≤base) (hgap : gap≤base)
    (first : RecordSpec) (records : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool)
    (hw : PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail≤base)
    (hg : totalGap (first::records)≤base) (hv : totalWidth (first::records)≤base) :
    originalHomeFee j first records nxTail dxTail nyTail dyTail gap≤72*base^2 := by
  have hl : originalHomeFee j first records nxTail dxTail nyTail dyTail gap≤72*base := by
    unfold originalHomeFee; omega
  exact hl.trans (Nat.mul_le_mul_left 72 (linear_square base hone))

theorem serializer_time_le (base a b : Nat) (hone : 1≤base)
    (ha : (PA17TMRatArithmeticPairEncode017.payload a).length≤base)
    (hb : (PA17TMRatArithmeticPairEncode017.payload b).length≤base) :
    64*((PA17TMRatArithmeticPairEncode017.payload a).length+
      (PA17TMRatArithmeticPairEncode017.payload b).length+1)^2≤576*base^2 := by
  have hs := Nat.pow_le_pow_left (show (PA17TMRatArithmeticPairEncode017.payload a).length+
    (PA17TMRatArithmeticPairEncode017.payload b).length+1≤3*base by omega) 2
  nlinarith

theorem locator_time_le (base total sourceLater : Nat) (hone : 1≤base)
    (htotal : total≤2*base) (hsource : sourceLater≤base) (before : List RecordSpec)
    (source : RecordSpec) (following : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool)
    (hw : PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail≤base)
    (hg : totalGap (before++source::following)≤base) (hv : totalWidth (before++source::following)≤base)
    (hsg : totalGap following≤base) (hsv : totalWidth following≤base) (hd : source.digits.length≤base) :
    locatorFee total sourceLater nxTail dxTail nyTail dyTail before source following≤68*base^2 := by
  have hl : locatorFee total sourceLater nxTail dxTail nyTail dyTail before source following≤68*base := by
    unfold locatorFee latestFee; omega
  exact hl.trans (Nat.mul_le_mul_left 68 (linear_square base hone))

theorem kernel_times_le (base j width aWidth gap : Nat) (hone : 1≤base)
    (records : List RecordSpec) (hj : j≤base) (hw : width≤base) (ha : aWidth≤base) (hgap : gap≤base)
    (hg : totalGap records≤base) (hv : totalWidth records≤base) :
    cachedPlainTime j records width gap≤256*base^2 ∧
      cachedSharedTime j records width aWidth gap≤256*base^2 := by
  let cost := cachedCost j records
  have hc : cost≤23*base := by unfold cost cachedCost; omega
  have hs := Nat.pow_le_pow_left hw 2
  have hp := Nat.mul_le_mul (show 2*cost+2*gap+45≤93*base by omega) hw
  have hq := Nat.mul_le_mul (show 2*cost+2*gap+4*aWidth+55≤107*base by omega) hw
  have hl : 2*cost+3*gap+totalGap records+2*totalWidth records+9*j+43≤104*base := by omega
  have hk : 2*cost+3*gap+6*aWidth+totalGap records+2*totalWidth records+9*j+56≤123*base := by omega
  have hb := linear_square base hone
  constructor
  · change 4*width^2+(2*cost+2*gap+45)*width+
      2*cost+3*gap+totalGap records+2*totalWidth records+9*j+43≤256*base^2
    nlinarith
  · change 4*width^2+(2*cost+2*gap+4*aWidth+55)*width+
      2*cost+3*gap+6*aWidth+totalGap records+2*totalWidth records+9*j+56≤256*base^2
    nlinarith

theorem original_pair_time_le (base j gap a b : Nat) (hone : 1≤base) (hj : j≤base) (hgap : gap≤base)
    (fieldA fieldB : SourceField) (memory : Nat) (first : RecordSpec) (records : List RecordSpec)
    (nxTail dxTail nyTail dyTail : List Bool)
    (hw : PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail≤base)
    (hg : totalGap (first::records)≤base) (hv : totalWidth (first::records)≤base)
    (ha : (PA17TMRatArithmeticPairEncode017.payload a).length≤base)
    (hb : (PA17TMRatArithmeticPairEncode017.payload b).length≤base) :
    originalPairTime fieldA fieldB memory j first records nxTail dxTail nyTail dyTail gap a b≤4096*base^2 := by
  have hfirst := original_row_time_le base j gap hone hj hgap fieldA .plain first records
    nxTail dxTail nyTail dyTail [] hw hg hv (by simp)
  have hA : (restoredDigits fieldA memory nxTail dxTail nyTail dyTail).length≤base := by
    simpa only [restoredDigits,List.length_cons] using
      (source_length_le_width fieldA nxTail dxTail nyTail dyTail).trans hw
  have hsecond := original_row_time_le base j gap hone hj hgap fieldB .shared first records
    nxTail dxTail nyTail dyTail (restoredDigits fieldA memory nxTail dxTail nyTail dyTail) hw hg hv hA
  have hhome := home_time_le base j gap hone hj hgap first records nxTail dxTail nyTail dyTail hw hg hv
  have hserialize := serializer_time_le base a b hone ha hb
  unfold originalPairTime
  omega

theorem gap_sum_append (before after : List RecordSpec) : totalGap (before++after)=totalGap before+totalGap after := by
  induction before with
  | nil => simp only [List.nil_append,totalGap,Nat.zero_add]
  | cons record before ih => simp only [List.cons_append,totalGap,ih,Nat.add_assoc]

theorem width_sum_append (before after : List RecordSpec) : totalWidth (before++after)=totalWidth before+totalWidth after := by
  induction before with
  | nil => simp only [List.nil_append,totalWidth,Nat.zero_add]
  | cons record before ih => simp only [List.cons_append,totalWidth,ih,Nat.add_assoc]

theorem selected_bounds (base j : Nat) (first : RecordSpec) (records before : List RecordSpec)
    (source : RecordSpec) (following : List RecordSpec) (hj : records.length=j)
    (hbank : before++source::following=first::records) (hgap : totalGap (first::records)≤base)
    (hwidth : totalWidth (first::records)≤base) :
    following.length≤j ∧ totalGap following≤base ∧ totalWidth following≤base ∧ source.digits.length≤base := by
  have hn := congrArg List.length hbank
  have hg := congrArg totalGap hbank
  have hv := congrArg totalWidth hbank
  simp only [List.length_append,List.length_cons,hj] at hn
  rw [gap_sum_append] at hg
  rw [width_sum_append] at hv
  simp only [totalGap,totalWidth] at hg hv hgap hwidth
  omega

theorem tail_succ_le (digits : List Bool) (hne : digits≠[]) (base : Nat) (hw : digits.length≤base) :
    digits.tail.length+1≤base := by
  cases digits with
  | nil => exact False.elim (hne rfl)
  | cons bit tail => exact hw

theorem cached_pair_time_le (base j aLater bLater gap a b : Nat) (hone : 1≤base) (hj : j≤base) (hgap : gap≤base)
    (first : RecordSpec) (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hcount : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (haLater : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hbLater : followingB.length=bLater)
    (hneA : sourceA.digits≠[]) (hneB : sourceB.digits≠[]) (nxTail dxTail nyTail dyTail : List Bool)
    (hw : PA17TMRatArithmeticFarLoad031.bankWidth nxTail dxTail nyTail dyTail≤base)
    (hg : totalGap (first::records)≤base) (hv : totalWidth (first::records)≤base)
    (ha : (PA17TMRatArithmeticPairEncode017.payload a).length≤base)
    (hb : (PA17TMRatArithmeticPairEncode017.payload b).length≤base) :
    cachedPairTime j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
      nxTail dxTail nyTail dyTail gap a b≤4096*base^2 := by
  obtain ⟨hlA,hgA,hvA,hdA⟩ := selected_bounds base j first records beforeA sourceA followingA hcount hbankA hg hv
  obtain ⟨hlB,hgB,hvB,hdB⟩ := selected_bounds base j first records beforeB sourceB followingB hcount hbankB hg hv
  have hmA := tail_succ_le sourceA.digits hneA base hdA
  have hmB := tail_succ_le sourceB.digits hneB base hdB
  have ht : j+1≤2*base := by omega
  have hlocA := locator_time_le base (j+1) aLater hone ht (by omega) beforeA sourceA followingA
    nxTail dxTail nyTail dyTail hw (by rw [hbankA]; exact hg) (by rw [hbankA]; exact hv) hgA hvA hdA
  have hlocB := locator_time_le base (j+1) bLater hone ht (by omega) beforeB sourceB followingB
    nxTail dxTail nyTail dyTail hw (by rw [hbankB]; exact hg) (by rw [hbankB]; exact hv) hgB hvB hdB
  have hplain := (kernel_times_le base aLater (sourceA.digits.tail.length+1) 0 gap hone followingA
    (by omega) hmA (by omega) hgap hgA hvA).1
  have hshared := (kernel_times_le base bLater (sourceB.digits.tail.length+1) sourceA.digits.length gap hone followingB
    (by omega) hmB hdA hgap hgB hvB).2
  have hhome := home_time_le base j gap hone hj hgap first records nxTail dxTail nyTail dyTail hw hg hv
  have hserialize := serializer_time_le base a b hone ha hb
  unfold cachedPairTime
  omega

def chargeBase (k width : Nat) : Nat := 64*(k+1)*(width+1)^2
def feeConstant (k : Nat) : Nat := 16777216*(k+1)^2
def pairConstant : Nat := 3*feeConstant PA17TMRatArithmeticWideCache045.allocationK

theorem pairConstant_pos : 0<pairConstant := by unfold pairConstant feeConstant; positivity

/-- The only five-record bound used by the scalar multiplication schedule.
Its hypotheses are preserved actual native/store poststate metadata. -/
theorem produced_bank_bounds (k width j : Nat) (records : List RecordSpec) (hcount : records.length≤5) (hj : j≤4)
    (hg : ∀ r∈records,r.gap≤2*k*width^2) (hv : ∀ r∈records,r.digits.length≤width) :
    1≤chargeBase k width ∧ width≤chargeBase k width ∧ j≤chargeBase k width ∧ k*width^2≤chargeBase k width ∧
      totalGap records≤chargeBase k width ∧ totalWidth records≤chargeBase k width := by
  have hp : 1≤(width+1)^2 := by
    have h : 0<(width+1)^2 := by positivity
    omega
  have hw : width≤(width+1)^2 := by nlinarith
  have hlow : 64*(width+1)^2≤chargeBase k width :=
    Nat.mul_le_mul_right _ (by omega : 64≤64*(k+1))
  have hs := Nat.pow_le_pow_left (show width≤width+1 by omega) 2
  have hgap : 10*k*width^2≤chargeBase k width := by
    calc
      _ ≤ 10*k*(width+1)^2 := Nat.mul_le_mul_left _ hs
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega : 10*k≤64*(k+1))
  obtain ⟨hgs,hvs⟩ := bank_sum_bounds records (2*k*width^2) width hg hv
  have hg5 : totalGap records≤10*k*width^2 := by
    calc
      _ ≤ records.length*(2*k*width^2) := hgs
      _ ≤ 5*(2*k*width^2) := Nat.mul_le_mul_right _ hcount
      _ = _ := by ring
  have hv5 : totalWidth records≤5*width := hvs.trans (Nat.mul_le_mul_right width hcount)
  refine ⟨by nlinarith,by nlinarith,by nlinarith,?_,hg5.trans hgap,?_⟩
  · calc
      _ ≤ 10*k*width^2 := by nlinarith [Nat.zero_le (k*width^2)]
      _ ≤ _ := hgap
  · exact hv5.trans (by nlinarith)

theorem cap_original_input (k : Nat) (x y : Rat) :
    4096*(chargeBase k (fieldWidth x y))^2≤feeConstant k*((encode [.rational x,.rational y]).length+1)^4 := by
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right (original_width_le_input x y) 1) 4
  calc
    _ = feeConstant k*(fieldWidth x y+1)^4 := by unfold chargeBase feeConstant; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hp

theorem original_fee_polynomial (k j : Nat) (hj : j≤4) (memory : Nat) (x y : Rat)
    (first : RecordSpec) (records : List RecordSpec) (hcount : records.length=j)
    (hg : ∀ r∈first::records,r.gap≤2*k*(fieldWidth x y)^2)
    (hv : ∀ r∈first::records,r.digits.length≤fieldWidth x y) :
    denominatorFee memory j x y first records (k*(fieldWidth x y)^2)≤
      feeConstant k*((encode [.rational x,.rational y]).length+1)^4 := by
  obtain ⟨hone,hw,hjB,hgap,hgB,hvB⟩ := produced_bank_bounds k (fieldWidth x y) j (first::records)
    (by simp only [List.length_cons,hcount]; omega) hj hg hv
  have hwidth := original_source_width x y
  have ha : (PA17TMRatArithmeticPairEncode017.payload x.den).length≤fieldWidth x y := by
    simpa only [PA17TMRatArithmeticPairEncode017.payload,PSTRTMNatValue017.rawPayload,List.length_ofFn] using
      (original_field_bits x y).2.2.1
  have hb : (PA17TMRatArithmeticPairEncode017.payload y.den).length≤fieldWidth x y := by
    simpa only [PA17TMRatArithmeticPairEncode017.payload,PSTRTMNatValue017.rawPayload,List.length_ofFn] using
      (original_field_bits x y).2.2.2
  have ht := original_pair_time_le (chargeBase k (fieldWidth x y)) j (k*(fieldWidth x y)^2) x.den y.den
    hone hjB hgap .dx .dy memory first records (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail (by rw [hwidth]; exact hw) hgB hvB (ha.trans hw) (hb.trans hw)
  exact (original_pair_fee_le .dx .dy memory j first records (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail (k*(fieldWidth x y)^2) x.den y.den).trans
      (ht.trans (cap_original_input k x y))

theorem cached_fees_polynomial (k j aLater bLater : Nat) (hj : j≤4) (x y : Rat) (first : RecordSpec)
    (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hcount : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (haLater : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hbLater : followingB.length=bLater)
    (hg : ∀ r∈first::records,r.gap≤2*k*(fieldWidth x y)^2)
    (hv : ∀ r∈first::records,r.digits.length≤fieldWidth x y) (a b : Nat)
    (ha : sourceA.digits=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : sourceB.digits=PA17TMRatArithmeticPairEncode017.payload b) :
    cachedPairFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
        (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
        (k*(fieldWidth x y)^2) a b≤feeConstant k*((encode [.rational x,.rational y]).length+1)^4 ∧
      cachedReadyFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
        (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
        (k*(fieldWidth x y)^2)≤feeConstant k*((encode [.rational x,.rational y]).length+1)^4 := by
  obtain ⟨hone,hw,hjB,hgap,hgB,hvB⟩ := produced_bank_bounds k (fieldWidth x y) j (first::records)
    (by simp only [List.length_cons,hcount]; omega) hj hg hv
  have hneA : sourceA.digits≠[] := by rw [ha]; exact PA17TMRatArithmeticFlagZero028.payload_ne_nil a
  have hneB : sourceB.digits≠[] := by rw [hb]; exact PA17TMRatArithmeticFlagZero028.payload_ne_nil b
  have hA := (selected_bounds _ j first records beforeA sourceA followingA hcount hbankA hgB hvB).2.2.2
  have hB := (selected_bounds _ j first records beforeB sourceB followingB hcount hbankB hgB hvB).2.2.2
  have hpa : (PA17TMRatArithmeticPairEncode017.payload a).length≤chargeBase k (fieldWidth x y) := by rw [←ha]; exact hA
  have hpb : (PA17TMRatArithmeticPairEncode017.payload b).length≤chargeBase k (fieldWidth x y) := by rw [←hb]; exact hB
  have ht := cached_pair_time_le (chargeBase k (fieldWidth x y)) j aLater bLater (k*(fieldWidth x y)^2) a b
    hone hjB hgap first records beforeA sourceA followingA beforeB sourceB followingB hcount hbankA haLater hbankB hbLater
    hneA hneB (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    (by rw [original_source_width]; exact hw) hgB hvB hpa hpb
  have hfee := (cached_pair_fee_le j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    (k*(fieldWidth x y)^2) a b).trans (ht.trans (cap_original_input k x y))
  refine ⟨hfee,?_⟩
  unfold cachedPairFee at hfee
  omega

/-- A consumer supplies its already-proved actual54 trace. The witness
below is exactly that same trace, with every prefix charged to the
ORIGINAL two-Rat input. This resource lemma creates no new program/input. -/
theorem same_actual_trace {states : Nat} (machine : Machine states) (x y : Rat)
    (start final : MachineState states) (trace : List (MachineState states))
    (actual : PSTRTMSeq005.RunsFrom machine start trace final) (fee : Nat)
    (ht : trace.length≤fee)
    (hfee : fee≤feeConstant PA17TMRatArithmeticWideCache045.allocationK*
      ((encode [.rational x,.rational y]).length+1)^4) :
    ∃ sameTrace, sameTrace=trace ∧ PSTRTMSeq005.RunsFrom machine start sameTrace final ∧
      sameTrace.length≤pairConstant*((encode [.rational x,.rational y]).length+1)^4 ∧
      ∀ k, visitedSpace machine (encode [.rational x,.rational y]).length (sameTrace.take k)≤
        pairConstant*((encode [.rational x,.rational y]).length+1)^4 := by
  let inputLength := (encode [.rational x,.rational y]).length
  let power := (inputLength+1)^4
  let c := feeConstant PA17TMRatArithmeticWideCache045.allocationK
  have hc : 1≤c := by
    have h : 0<c := by
      unfold c feeConstant
      positivity
    omega
  have hp : inputLength+1≤power := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : (1 : Nat) ≤ inputLength + 1) (by decide : (1 : Nat)≤4)
  refine ⟨trace,rfl,actual,?_,?_⟩
  · change trace.length≤3*c*power
    have h := ht.trans hfee
    change trace.length≤c*power at h
    nlinarith
  · intro k
    have hs := PSTRTMTrace002.visitedSpace_le machine inputLength (trace.take k)
    have hk : (trace.take k).length≤trace.length := by simp only [List.length_take]; omega
    change visitedSpace machine inputLength (trace.take k)≤3*c*power
    change fee≤c*power at hfee
    have hcp : power≤c*power := by nlinarith
    nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairBounds061
