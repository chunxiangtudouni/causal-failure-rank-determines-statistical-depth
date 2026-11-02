module
public import Structure.PA17_TM_RatArithmetic_RatDivFields_066a
public import Structure.PA17_TM_RatArithmetic_MulSuffix_063d

/-! The already-frozen Boolean program, entered at its actual phase4,
normalizes the DIV-produced M/D records. This file supplies real GCD runs;
no new machine or original-input qualification is introduced. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivSuffix069

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedOuter043
open PA17TMRatArithmeticMulFields048 (fieldWidth_ge_four)
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticAllocationBounds056
open PA17TMRatArithmeticCachedPair054 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticMulClosure059 PA17TMRatArithmeticMulController057
open PA17TMRatArithmeticPairBounds061 PA17TMRatArithmeticRatDivFields066
open PA17TMRatArithmeticMulSuffix063
  (record_payload_length record_width_le original_source_bankWidth)

attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticCachedOuter043.carryCap PA17TMRatArithmeticCachedPair054.cachedPairCap
  PA17TMRatArithmeticNativeTail055.carriedTailCap PA17TMRatArithmeticNativeTail055.tailCap

def originalPower (x y : Rat) : Nat := ((encode [.rational x,.rational y]).length+1)^4
def roundCoefficient : Nat := allocationCoefficient+feeConstant allocationK+nativeCoefficient

def mRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (divMagnitude x y)
def dRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (divDenominator x y)
def gRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (divNormalizer x y)
def uRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (divNumerator x y)
def vRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (divReducedDenominator x y)

theorem g_segment (x y : Rat) (memory : Fin 64) (gapM gapD : Nat)
    (hM : gapM≤2*allocationK*(fieldWidth x y)^2)
    (hD : gapD≤2*allocationK*(fieldWidth x y)^2) :
    ∃ gapG trace last, 6≤gapG ∧ gapG≤2*allocationK*(fieldWidth x y)^2 ∧
      Segment mulMachine
        (entryCfg (4 : Fin 17) (widen64 memory)
          (bankHeader x y [mRecord x y gapM,dRecord x y gapD])) trace last ∧
      TM0.step mulMachine last=some
        (entryCfg (7 : Fin 17) (widen64 memory)
          (bankHeader x y [mRecord x y gapM,dRecord x y gapD,gRecord x y gapG])) ∧
      trace.length≤roundCoefficient*originalPower x y := by
  let m := mRecord x y gapM
  let d := dRecord x y gapD
  let w := fieldWidth x y
  let gap := allocationK*w^2
  let n := (encode [.rational x,.rational y]).length+1
  have hw : 1≤w := by have h:=fieldWidth_ge_four x y;omega
  have hwn : w≤n := by have h:=original_width_le_input x y;omega
  have hn : 1≤n := by omega
  have hg : ∀ r∈[m,d],r.gap≤2*allocationK*w^2 := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact hM
    · exact hD
  have hv : ∀ r∈[m,d],r.digits.length≤w := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact record_width_le _ _ _ (divMagnitude_bits x y)
    · exact record_width_le _ _ _ (divDenominator_bits x y)
  obtain ⟨tr4,run4,len4,_space4⟩ := actual_allocation_contract 63 2 memory [m,d] rfl (by decide) x y hg hv
  rw [allocated_is_work x y m [d] gap] at run4
  change PSTRTMSeq005.RunsFrom (component (4 : Fin 17)).code
    ⟨label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 2 allocationK+1)),bankHeader x y [m,d]⟩ tr4
    ⟨(carryFinal 63 2 allocationK memory (bankWork x y m [d] gap)).q,bankWork x y m [d] gap⟩ at run4
  obtain ⟨tr5,run5,len5,_space5⟩ := cached_pair_contract 63 1 1 0 memory m [d] [] m [d] [m] d []
    rfl rfl rfl rfl rfl
    (PA17TMRatArithmeticPairEncode017.payload (divMagnitude x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (divDenominator x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (divMagnitude x y)).tail
    (PA17TMRatArithmeticPairEncode017.payload (divDenominator x y)).tail
    (canonical_head_tail _) (canonical_head_tail _) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    gap (divMagnitude x y) (divDenominator x y) rfl rfl
  change PSTRTMSeq005.RunsFrom (component (5 : Fin 17)).code
    ⟨label memory (0 : Fin (cachedPairCap 1 1 0+1)),bankWork x y m [d] gap⟩ tr5
    ⟨label memory (cachedPairPort 1 1 0),bankNative x y m [d] gap (divMagnitude x y) (divDenominator x y)⟩ at run5
  have actual := gcd_allocated_runsFrom (divMagnitude x y) (divDenominator x y) w
    (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [d]) hw (five_scales x y).2.2.1
  obtain ⟨gapG,tr6,lower,upper,run6,len6,_space6⟩ := carriedTail_contract 63 ROOTTMGCDDispatch018.nativeGcdMachine
    1 memory m [d] rfl (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail gap
    (divMagnitude x y) (divDenominator x y) (divNormalizer x y) actual
  rw [←native_is_tail_input,tail_output_is_header] at run6
  change PSTRTMSeq005.RunsFrom (component (6 : Fin 17)).code
    ⟨carriedTailEntry 63 3564 1 memory,bankNative x y m [d] gap (divMagnitude x y) (divDenominator x y)⟩ tr6
    ⟨carriedTailPort 63 3564 1 memory,bankHeader x y [m,d,gRecord x y gapG]⟩ at run6
  have gapGbound : gapG≤2*allocationK*w^2 := new_gap_bound _ _ w gapG hw (five_scales x y).2.2.1 upper
  have entry4 : (component (4 : Fin 17)).entry (widen64 memory)=
      label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 2 allocationK+1)) := row64_entry _ _ memory
  have entry5 : (component (5 : Fin 17)).entry (widen64 memory)=
      label memory (0 : Fin (cachedPairCap 1 1 0+1)) := row64_entry _ _ memory
  have entry6 : (component (6 : Fin 17)).entry (widen64 memory)=carriedTailEntry 63 3564 1 memory := row64_entry _ _ memory
  have seg4 := component_segment (4 : Fin 17) _ _ _ run4
  have seg5 := component_segment (5 : Fin 17) _ _ _ run5
  have seg6 := component_segment (6 : Fin 17) _ _ _ run6
  have decode4 : (component (4 : Fin 17)).decode
      (carryFinal 63 2 allocationK memory (bankWork x y m [d] gap)).q=widen64 memory := allocation64_decode 2 memory _
  have decode5 : (component (5 : Fin 17)).decode (label memory (cachedPairPort 1 1 0))=widen64 memory :=
    cached_decode 1 1 0 memory
  have decode6 : (component (6 : Fin 17)).decode (carriedTailPort 63 3564 1 memory)=widen64 memory :=
    tail_decode ROOTTMGCDDispatch018.nativeGcdMachine 1 memory
  have step4 := paid_transfer (4 : Fin 17) (by decide) _ run4.2.2.2
  have step5 := paid_transfer (5 : Fin 17) (by decide) _ run5.2.2.2
  have step6 := paid_transfer (6 : Fin 17) (by decide) _ run6.2.2.2
  rw [decode4] at step4
  rw [decode5] at step5
  rw [decode6] at step6
  change TM0.step mulMachine _=some (entryCfg (5 : Fin 17) (widen64 memory) (bankWork x y m [d] gap)) at step4
  change TM0.step mulMachine _=some (entryCfg (6 : Fin 17) (widen64 memory)
    (bankNative x y m [d] gap (divMagnitude x y) (divDenominator x y))) at step5
  change TM0.step mulMachine _=some (entryCfg (7 : Fin 17) (widen64 memory)
    (bankHeader x y [m,d,gRecord x y gapG])) at step6
  have step4' : TM0.step mulMachine
      (liftCfg (4 : Fin 17) ⟨(carryFinal 63 2 allocationK memory (bankWork x y m [d] gap)).q,bankWork x y m [d] gap⟩)=
      some (liftCfg (5 : Fin 17) ⟨label memory (0 : Fin (cachedPairCap 1 1 0+1)),bankWork x y m [d] gap⟩) := by
    simpa only [entryCfg,entry5] using step4
  have step5' : TM0.step mulMachine
      (liftCfg (5 : Fin 17) ⟨label memory (cachedPairPort 1 1 0),bankNative x y m [d] gap (divMagnitude x y) (divDenominator x y)⟩)=
      some (liftCfg (6 : Fin 17) ⟨carriedTailEntry 63 3564 1 memory,bankNative x y m [d] gap (divMagnitude x y) (divDenominator x y)⟩) := by
    simpa only [entryCfg,entry6] using step5
  have joined45 := segment_append mulMachine _ _ _ _ _ _ seg4 seg5 step4'
  have joined := segment_append mulMachine _ _ _ _ _ _ joined45 seg6 step5'
  obtain ⟨bankGap,bankWidthBound⟩ := cache_totals_le 2 [m,d] rfl (by decide) x y hg hv
  have fee5 := (cached_fees_polynomial allocationK 1 1 0 (by decide) x y m [d] [] m [d] [m] d []
    rfl rfl rfl rfl rfl hg hv (divMagnitude x y) (divDenominator x y) rfl rfl).1
  have fee6 := native_tail_fee_le 1 (by decide) m [d]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
    gapG (divMagnitude x y) (divDenominator x y) (divNormalizer x y) w n
    bankGap bankWidthBound gapGbound (five_scales x y).2.2.1 (divNormalizer_bits x y)
    (by rw [original_source_bankWidth]) hwn hn
  let trace := (liftTrace (4 : Fin 17) tr4++liftTrace (5 : Fin 17) tr5)++liftTrace (6 : Fin 17) tr6
  have ht4 : (liftTrace (4 : Fin 17) tr4).length=tr4.length := liftTrace_length _ _
  have ht5 : (liftTrace (5 : Fin 17) tr5).length=tr5.length := liftTrace_length _ _
  have ht6 : (liftTrace (6 : Fin 17) tr6).length=tr6.length := liftTrace_length _ _
  have length : trace.length≤roundCoefficient*originalPower x y := by
    dsimp only [trace]
    simp only [List.length_append]
    rw [ht4,ht5,ht6]
    have h4 := len4
    have h5 := len5.trans fee5
    have h6 := len6.trans fee6
    change tr4.length≤allocationCoefficient*n^4 at h4
    change tr5.length≤feeConstant allocationK*n^4 at h5
    change tr6.length≤nativeCoefficient*n^4 at h6
    change _≤roundCoefficient*n^4
    calc
      _ ≤ allocationCoefficient*n^4+feeConstant allocationK*n^4+nativeCoefficient*n^4 :=
        Nat.add_le_add (Nat.add_le_add h4 h5) h6
      _ = _ := by unfold roundCoefficient;ring
  refine ⟨gapG,trace,_,lower,gapGbound,?_,step6,length⟩
  simpa only [entryCfg,entry4] using joined


/-! Actual U quotient in the same frozen phases7..9. -/
theorem u_segment (x y : Rat) (memory : Fin 64) (gapM gapD gapG : Nat)
    (hM : gapM≤2*allocationK*(fieldWidth x y)^2)
    (hD : gapD≤2*allocationK*(fieldWidth x y)^2)
    (hG : gapG≤2*allocationK*(fieldWidth x y)^2) :
    ∃ gapU trace last, 6≤gapU ∧ gapU≤2*allocationK*(fieldWidth x y)^2 ∧
      Segment mulMachine
        (entryCfg (7 : Fin 17) (widen64 memory)
          (bankHeader x y [mRecord x y gapM,dRecord x y gapD,gRecord x y gapG])) trace last ∧
      TM0.step mulMachine last=some
        (entryCfg (10 : Fin 17) (widen64 memory)
          (bankHeader x y [mRecord x y gapM,dRecord x y gapD,gRecord x y gapG,uRecord x y gapU])) ∧
      trace.length≤roundCoefficient*originalPower x y := by
  let m := mRecord x y gapM
  let d := dRecord x y gapD
  let g := gRecord x y gapG
  let w := fieldWidth x y
  let gap := allocationK*w^2
  let n := (encode [.rational x,.rational y]).length+1
  have hw : 1≤w := by have h:=fieldWidth_ge_four x y;omega
  have hwn : w≤n := by have h:=original_width_le_input x y;omega
  have hn : 1≤n := by omega
  have hg : ∀ r∈[m,d,g],r.gap≤2*allocationK*w^2 := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact hM
    · exact hD
    · exact hG
  have hv : ∀ r∈[m,d,g],r.digits.length≤w := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact record_width_le gapM (divMagnitude x y) w (divMagnitude_bits x y)
    · exact record_width_le gapD (divDenominator x y) w (divDenominator_bits x y)
    · exact record_width_le gapG (divNormalizer x y) w (divNormalizer_bits x y)
  obtain ⟨tr7,run7,len7,_space7⟩ := actual_allocation_contract 63 3 memory [m,d,g] rfl (by decide) x y hg hv
  rw [allocated_is_work x y m [d,g] gap] at run7
  change PSTRTMSeq005.RunsFrom (component (7 : Fin 17)).code
    ⟨label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 3 allocationK+1)),bankHeader x y [m,d,g]⟩ tr7
    ⟨(carryFinal 63 3 allocationK memory (bankWork x y m [d,g] gap)).q,bankWork x y m [d,g] gap⟩ at run7
  obtain ⟨tr8,run8,len8,_space8⟩ := cached_pair_contract 63 2 2 0 memory m [d,g] [] m [d,g] [m,d] g []
    rfl rfl rfl rfl rfl
    (PA17TMRatArithmeticPairEncode017.payload (divMagnitude x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (divNormalizer x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (divMagnitude x y)).tail
    (PA17TMRatArithmeticPairEncode017.payload (divNormalizer x y)).tail
    (canonical_head_tail _) (canonical_head_tail _) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    gap (divMagnitude x y) (divNormalizer x y) rfl rfl
  change PSTRTMSeq005.RunsFrom (component (8 : Fin 17)).code
    ⟨label memory (0 : Fin (cachedPairCap 2 2 0+1)),bankWork x y m [d,g] gap⟩ tr8
    ⟨label memory (cachedPairPort 2 2 0),bankNative x y m [d,g] gap (divMagnitude x y) (divNormalizer x y)⟩ at run8
  have actual := quotient_allocated_runsFrom (divMagnitude x y) (divNormalizer x y) w
    (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [d,g]) hw (five_scales x y).2.2.2.1
  obtain ⟨gapU,tr9,lower,upper,run9,len9,_space9⟩ := carriedTail_contract 63 PA17TMDivisionFull012.quotientMachine
    2 memory m [d,g] rfl (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail gap
    (divMagnitude x y) (divNormalizer x y) (divNumerator x y) actual
  rw [←native_is_tail_input,tail_output_is_header] at run9
  change PSTRTMSeq005.RunsFrom (component (9 : Fin 17)).code
    ⟨carriedTailEntry 63 1136 2 memory,bankNative x y m [d,g] gap (divMagnitude x y) (divNormalizer x y)⟩ tr9
    ⟨carriedTailPort 63 1136 2 memory,bankHeader x y [m,d,g,uRecord x y gapU]⟩ at run9
  have gapUbound : gapU≤2*allocationK*w^2 := new_gap_bound _ _ w gapU hw (five_scales x y).2.2.2.1 upper
  have entry7 : (component (7 : Fin 17)).entry (widen64 memory)=
      label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 3 allocationK+1)) := row64_entry _ _ memory
  have entry8 : (component (8 : Fin 17)).entry (widen64 memory)=
      label memory (0 : Fin (cachedPairCap 2 2 0+1)) := row64_entry _ _ memory
  have entry9 : (component (9 : Fin 17)).entry (widen64 memory)=carriedTailEntry 63 1136 2 memory := row64_entry _ _ memory
  have seg7 := component_segment (7 : Fin 17) _ _ _ run7
  have seg8 := component_segment (8 : Fin 17) _ _ _ run8
  have seg9 := component_segment (9 : Fin 17) _ _ _ run9
  have decode7 : (component (7 : Fin 17)).decode
      (carryFinal 63 3 allocationK memory (bankWork x y m [d,g] gap)).q=widen64 memory :=
    allocation64_decode 3 memory _
  have decode8 : (component (8 : Fin 17)).decode (label memory (cachedPairPort 2 2 0))=widen64 memory :=
    cached_decode 2 2 0 memory
  have decode9 : (component (9 : Fin 17)).decode (carriedTailPort 63 1136 2 memory)=widen64 memory :=
    tail_decode PA17TMDivisionFull012.quotientMachine 2 memory
  have step7 := paid_transfer (7 : Fin 17) (by decide) _ run7.2.2.2
  have step8 := paid_transfer (8 : Fin 17) (by decide) _ run8.2.2.2
  have step9 := paid_transfer (9 : Fin 17) (by decide) _ run9.2.2.2
  rw [decode7] at step7
  rw [decode8] at step8
  rw [decode9] at step9
  change TM0.step mulMachine _=some (entryCfg (8 : Fin 17) (widen64 memory) (bankWork x y m [d,g] gap)) at step7
  change TM0.step mulMachine _=some (entryCfg (9 : Fin 17) (widen64 memory)
    (bankNative x y m [d,g] gap (divMagnitude x y) (divNormalizer x y))) at step8
  change TM0.step mulMachine _=some (entryCfg (10 : Fin 17) (widen64 memory)
    (bankHeader x y [m,d,g,uRecord x y gapU])) at step9
  have step7' : TM0.step mulMachine (liftCfg (7 : Fin 17)
      ⟨(carryFinal 63 3 allocationK memory (bankWork x y m [d,g] gap)).q,bankWork x y m [d,g] gap⟩)=some (liftCfg (8 : Fin 17)
      ⟨label memory (0 : Fin (cachedPairCap 2 2 0+1)),bankWork x y m [d,g] gap⟩) := by
    simpa only [entryCfg,entry8] using step7
  have step8' : TM0.step mulMachine (liftCfg (8 : Fin 17)
      ⟨label memory (cachedPairPort 2 2 0),bankNative x y m [d,g] gap (divMagnitude x y) (divNormalizer x y)⟩)=some (liftCfg (9 : Fin 17)
      ⟨carriedTailEntry 63 1136 2 memory,bankNative x y m [d,g] gap (divMagnitude x y) (divNormalizer x y)⟩) := by
    simpa only [entryCfg,entry9] using step8
  have joined78 := segment_append mulMachine _ _ _ _ _ _ seg7 seg8 step7'
  have joined := segment_append mulMachine _ _ _ _ _ _ joined78 seg9 step8'
  obtain ⟨bankGap,bankWidthBound⟩ := cache_totals_le 3 [m,d,g] rfl (by decide) x y hg hv
  have fee8 := (cached_fees_polynomial allocationK 2 2 0 (by decide) x y m [d,g] [] m [d,g] [m,d] g []
    rfl rfl rfl rfl rfl hg hv (divMagnitude x y) (divNormalizer x y) rfl rfl).1
  have fee9 := native_tail_fee_le 2 (by decide) m [d,g]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
    gapU (divMagnitude x y) (divNormalizer x y) (divNumerator x y) w n
    bankGap bankWidthBound gapUbound (five_scales x y).2.2.2.1 (div_quotient_bits x y).1
    (by rw [original_source_bankWidth]) hwn hn
  let trace := (liftTrace (7 : Fin 17) tr7++liftTrace (8 : Fin 17) tr8)++liftTrace (9 : Fin 17) tr9
  have ht7 : (liftTrace (7 : Fin 17) tr7).length=tr7.length := liftTrace_length (7 : Fin 17) tr7
  have ht8 : (liftTrace (8 : Fin 17) tr8).length=tr8.length := liftTrace_length (8 : Fin 17) tr8
  have ht9 : (liftTrace (9 : Fin 17) tr9).length=tr9.length := liftTrace_length (9 : Fin 17) tr9
  have length : trace.length≤roundCoefficient*originalPower x y := by
    simp only [trace,List.length_append]
    rw [ht7,ht8,ht9]
    have h7 := len7
    have h8 := len8.trans fee8
    have h9 := len9.trans fee9
    change tr7.length≤allocationCoefficient*n^4 at h7
    change tr8.length≤feeConstant allocationK*n^4 at h8
    change tr9.length≤nativeCoefficient*n^4 at h9
    change _≤roundCoefficient*n^4
    calc
      _ ≤ (allocationCoefficient*n^4+feeConstant allocationK*n^4)+nativeCoefficient*n^4 :=
        Nat.add_le_add (Nat.add_le_add h7 h8) h9
      _ = roundCoefficient*n^4 := by unfold roundCoefficient;ring
  refine ⟨gapU,trace,_,lower,gapUbound,?_,step9,length⟩
  simpa only [entryCfg,entry7] using joined


end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivSuffix069
