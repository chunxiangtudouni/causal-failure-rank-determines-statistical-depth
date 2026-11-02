module
public import Structure.PA17_TM_RatArithmetic_RatDivSuffix_069a

/-! Actual V recording and final U-zero/sign/cleanup on the same frozen
57 code. Only the internal observed nonzero-D branch invokes canonical
Rat division semantics. Original raw inputs are not requalified. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivSuffix069

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedOuter043
open PA17TMRatArithmeticMulFields048 (fieldWidth_ge_four fixed_bank_bounds)
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticAllocationBounds056
open PA17TMRatArithmeticCachedPair054 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticMulClosure059 PA17TMRatArithmeticMulController057
open PA17TMRatArithmeticPairBounds061 PA17TMRatArithmeticRatDivFields066
open PA17TMRatArithmeticReturnHome037 PA17TMRatArithmeticZeroCarry058 PA17TMRatArithmeticSignDispatch053
open PA17TMRatArithmeticMulSuffix063 (record_payload_length record_width_le original_source_bankWidth)
attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticCachedOuter043.carryCap PA17TMRatArithmeticCachedPair054.cachedPairCap
  PA17TMRatArithmeticCachedPair054.cachedReadyCap
  PA17TMRatArithmeticNativeTail055.carriedTailCap PA17TMRatArithmeticNativeTail055.tailCap
  PA17TMRatArithmeticZeroCarry058.observeCap PA17TMRatArithmeticSignDispatch053.dispatchCap

theorem actual_div_negative (x y : Rat) (hd : divDenominator x y≠0) :
    repairedNegative (observedMemory (PA17TMRatArithmeticMulStart049.actualMemory x y)
      (decide (divNumerator x y=0)))=sign (x/y) :=
  (actual_repaired_negative x y (divNumerator x y)).trans (normal_fields x y hd).2.2

def lastCacheTape (x y : Rat) (gapM gapD gapG gapU gapV : Nat) : Tape Bool :=
  homeInput (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
    (mRecord x y gapM) [dRecord x y gapD,gRecord x y gapG,uRecord x y gapU,vRecord x y gapV] []

theorem v_segment (x y : Rat) (memory : Fin 64) (gapM gapD gapG gapU : Nat)
    (hM : gapM≤2*allocationK*(fieldWidth x y)^2)
    (hD : gapD≤2*allocationK*(fieldWidth x y)^2)
    (hG : gapG≤2*allocationK*(fieldWidth x y)^2)
    (hU : gapU≤2*allocationK*(fieldWidth x y)^2) :
    ∃ gapV trace last, 6≤gapV ∧ gapV≤2*allocationK*(fieldWidth x y)^2 ∧
      Segment mulMachine
        (entryCfg (10 : Fin 17) (widen64 memory)
          (bankHeader x y [mRecord x y gapM,dRecord x y gapD,gRecord x y gapG,uRecord x y gapU])) trace last ∧
      TM0.step mulMachine last=some
        (entryCfg (13 : Fin 17) (widen64 memory) (lastCacheTape x y gapM gapD gapG gapU gapV)) ∧
      trace.length≤roundCoefficient*originalPower x y := by
  let m := mRecord x y gapM
  let d := dRecord x y gapD
  let g := gRecord x y gapG
  let u := uRecord x y gapU
  let w := fieldWidth x y
  let gap := allocationK*w^2
  let n := (encode [.rational x,.rational y]).length+1
  have hw : 1≤w := by have h:=fieldWidth_ge_four x y;omega
  have hwn : w≤n := by have h:=original_width_le_input x y;omega
  have hn : 1≤n := by omega
  have hg : ∀ r∈[m,d,g,u],r.gap≤2*allocationK*w^2 := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact hM
    · exact hD
    · exact hG
    · exact hU
  have hv : ∀ r∈[m,d,g,u],r.digits.length≤w := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · exact record_width_le gapM (divMagnitude x y) w (divMagnitude_bits x y)
    · exact record_width_le gapD (divDenominator x y) w (divDenominator_bits x y)
    · exact record_width_le gapG (divNormalizer x y) w (divNormalizer_bits x y)
    · exact record_width_le gapU (divNumerator x y) w (div_quotient_bits x y).1
  obtain ⟨tr10,run10,len10,_space10⟩ := actual_allocation_contract 63 4 memory [m,d,g,u] rfl (by decide) x y hg hv
  rw [allocated_is_work x y m [d,g,u] gap] at run10
  change PSTRTMSeq005.RunsFrom (component (10 : Fin 17)).code
    ⟨label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 4 allocationK+1)),bankHeader x y [m,d,g,u]⟩ tr10
    ⟨(carryFinal 63 4 allocationK memory (bankWork x y m [d,g,u] gap)).q,bankWork x y m [d,g,u] gap⟩ at run10
  obtain ⟨tr11,run11,len11,_space11⟩ := cached_pair_contract 63 3 2 1 memory m [d,g,u] [m] d [g,u] [m,d] g [u]
    rfl rfl rfl rfl rfl
    (PA17TMRatArithmeticPairEncode017.payload (divDenominator x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (divNormalizer x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (divDenominator x y)).tail
    (PA17TMRatArithmeticPairEncode017.payload (divNormalizer x y)).tail
    (canonical_head_tail _) (canonical_head_tail _) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    gap (divDenominator x y) (divNormalizer x y) rfl rfl
  change PSTRTMSeq005.RunsFrom (component (11 : Fin 17)).code
    ⟨label memory (0 : Fin (cachedPairCap 3 2 1+1)),bankWork x y m [d,g,u] gap⟩ tr11
    ⟨label memory (cachedPairPort 3 2 1),bankNative x y m [d,g,u] gap (divDenominator x y) (divNormalizer x y)⟩ at run11
  have actual := quotient_allocated_runsFrom (divDenominator x y) (divNormalizer x y) w
    (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [d,g,u]) hw (five_scales x y).2.2.2.2
  obtain ⟨gapV,trLocal,lastLocal,runLocal,lastTape,lower,upper,lenLocal,_spaceLocal⟩ := actual
  let output := lastCacheTape x y gapM gapD gapG gapU gapV
  have lastTape' : lastLocal.Tape=output :=
    lastTape.trans (newRecord_home (sign x) [false] (false::(numeratorDigits x).tail)
      (false::(denominatorDigits x).tail) (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
      m [d,g,u] gapV (divReducedDenominator x y))
  have lastEq : lastLocal=⟨lastLocal.q,output⟩ := by
    cases lastLocal with
    | mk q tape => exact congrArg (fun t => (⟨q,t⟩ : MachineState 1170)) lastTape'
  change PSTRTMSeq005.RunsFrom PA17TMRatArithmeticNativeCache030.quotientCacheMachine
    ⟨0,tailInput (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [d,g,u]
      gap (divDenominator x y) (divNormalizer x y)⟩ trLocal lastLocal at runLocal
  rw [←native_is_tail_input,lastEq] at runLocal
  have run12 := quotient_record_runs memory _ _ _ runLocal
  let tr12 := trLocal.map (blockCfg (s:=1170) memory)
  change PSTRTMSeq005.RunsFrom (component (12 : Fin 17)).code
    ⟨label memory (0 : Fin 1171),bankNative x y m [d,g,u] gap (divDenominator x y) (divNormalizer x y)⟩ tr12
    ⟨label memory lastLocal.q,output⟩ at run12
  have gapVbound : gapV≤2*allocationK*w^2 := new_gap_bound _ _ w gapV hw (five_scales x y).2.2.2.2 upper
  have entry10 : (component (10 : Fin 17)).entry (widen64 memory)=
      label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 4 allocationK+1)) := row64_entry _ _ memory
  have entry11 : (component (11 : Fin 17)).entry (widen64 memory)=
      label memory (0 : Fin (cachedPairCap 3 2 1+1)) := row64_entry _ _ memory
  have entry12 : (component (12 : Fin 17)).entry (widen64 memory)=label memory (0 : Fin 1171) := row64_entry _ _ memory
  have seg10 := component_segment (10 : Fin 17) _ _ _ run10
  have seg11 := component_segment (11 : Fin 17) _ _ _ run11
  have seg12 := component_segment (12 : Fin 17) _ _ _ run12
  have decode10 : (component (10 : Fin 17)).decode
      (carryFinal 63 4 allocationK memory (bankWork x y m [d,g,u] gap)).q=widen64 memory :=
    allocation64_decode 4 memory _
  have decode11 : (component (11 : Fin 17)).decode (label memory (cachedPairPort 3 2 1))=widen64 memory :=
    cached_decode 3 2 1 memory
  have decode12 : (component (12 : Fin 17)).decode (label memory lastLocal.q)=widen64 memory :=
    quotient_record_decode memory lastLocal.q
  have step10 := paid_transfer (10 : Fin 17) (by decide) _ run10.2.2.2
  have step11 := paid_transfer (11 : Fin 17) (by decide) _ run11.2.2.2
  have step12 := paid_transfer (12 : Fin 17) (by decide) _ run12.2.2.2
  rw [decode10] at step10
  rw [decode11] at step11
  rw [decode12] at step12
  change TM0.step mulMachine _=some (entryCfg (11 : Fin 17) (widen64 memory) (bankWork x y m [d,g,u] gap)) at step10
  change TM0.step mulMachine _=some (entryCfg (12 : Fin 17) (widen64 memory)
    (bankNative x y m [d,g,u] gap (divDenominator x y) (divNormalizer x y))) at step11
  change TM0.step mulMachine _=some (entryCfg (13 : Fin 17) (widen64 memory) output) at step12
  have step10' : TM0.step mulMachine (liftCfg (10 : Fin 17)
      ⟨(carryFinal 63 4 allocationK memory (bankWork x y m [d,g,u] gap)).q,bankWork x y m [d,g,u] gap⟩)=some (liftCfg (11 : Fin 17)
      ⟨label memory (0 : Fin (cachedPairCap 3 2 1+1)),bankWork x y m [d,g,u] gap⟩) := by
    simpa only [entryCfg,entry11] using step10
  have step11' : TM0.step mulMachine (liftCfg (11 : Fin 17)
      ⟨label memory (cachedPairPort 3 2 1),bankNative x y m [d,g,u] gap (divDenominator x y) (divNormalizer x y)⟩)=some (liftCfg (12 : Fin 17)
      ⟨label memory (0 : Fin 1171),bankNative x y m [d,g,u] gap (divDenominator x y) (divNormalizer x y)⟩) := by
    simpa only [entryCfg,entry12] using step11
  have joined1011 := segment_append mulMachine _ _ _ _ _ _ seg10 seg11 step10'
  have joined := segment_append mulMachine _ _ _ _ _ _ joined1011 seg12 step11'
  have fee11 := (cached_fees_polynomial allocationK 3 2 1 (by decide) x y m [d,g,u] [m] d [g,u] [m,d] g [u]
    rfl rfl rfl rfl rfl hg hv (divDenominator x y) (divNormalizer x y) rfl rfl).1
  have fee12 := native_v_fee_le (divDenominator x y) (divNormalizer x y) w n
    (five_scales x y).2.2.2.2 hwn hn
  let trace := (liftTrace (10 : Fin 17) tr10++liftTrace (11 : Fin 17) tr11)++liftTrace (12 : Fin 17) tr12
  have ht10 : (liftTrace (10 : Fin 17) tr10).length=tr10.length := liftTrace_length (10 : Fin 17) tr10
  have ht11 : (liftTrace (11 : Fin 17) tr11).length=tr11.length := liftTrace_length (11 : Fin 17) tr11
  have ht12 : (liftTrace (12 : Fin 17) tr12).length=tr12.length := liftTrace_length (12 : Fin 17) tr12
  have length : trace.length≤roundCoefficient*originalPower x y := by
    simp only [trace,List.length_append]
    rw [ht10,ht11,ht12]
    have h10 := len10
    have h11 := len11.trans fee11
    have h12 : tr12.length≤nativeCoefficient*n^4 := by
      simp only [tr12,List.length_map]
      exact lenLocal.trans fee12
    change tr10.length≤allocationCoefficient*n^4 at h10
    change tr11.length≤feeConstant allocationK*n^4 at h11
    change _≤roundCoefficient*n^4
    calc
      _ ≤ (allocationCoefficient*n^4+feeConstant allocationK*n^4)+nativeCoefficient*n^4 :=
        Nat.add_le_add (Nat.add_le_add h10 h11) h12
      _ = roundCoefficient*n^4 := by unfold roundCoefficient;ring
  refine ⟨gapV,trace,_,lower,gapVbound,?_,step12,length⟩
  simpa only [entryCfg,entry10] using joined


def finishCoefficient : Nat := 3*allocationCoefficient+feeConstant allocationK

theorem finish_segment (x y : Rat) (hd : divDenominator x y≠0) (gapM gapD gapG gapU gapV : Nat)
    (hM : gapM≤2*allocationK*(fieldWidth x y)^2)
    (hD : gapD≤2*allocationK*(fieldWidth x y)^2)
    (hG : gapG≤2*allocationK*(fieldWidth x y)^2)
    (hU : gapU≤2*allocationK*(fieldWidth x y)^2)
    (hV : gapV≤2*allocationK*(fieldWidth x y)^2) :
    ∃ trace last, PSTRTMSeq005.RunsFrom mulMachine
        (entryCfg (13 : Fin 17) (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y))
          (lastCacheTape x y gapM gapD gapG gapU gapV)) trace last ∧
      last.Tape=Tape.mk₁ (encode [.rational (x/y)]) ∧
      trace.length≤finishCoefficient*originalPower x y := by
  let m := mRecord x y gapM
  let d := dRecord x y gapD
  let g := gRecord x y gapG
  let u := uRecord x y gapU
  let v := vRecord x y gapV
  let oldMemory := PA17TMRatArithmeticMulStart049.actualMemory x y
  let memory := observedMemory oldMemory (decide (divNumerator x y=0))
  let w := fieldWidth x y
  let gap := allocationK*w^2
  let n := (encode [.rational x,.rational y]).length+1
  have hw : 1≤w := by have h:=fieldWidth_ge_four x y;omega
  have hwn : w≤n := by have h:=original_width_le_input x y;omega
  have hn : 1≤n := by omega
  have hg : ∀ r∈[m,d,g,u,v],r.gap≤2*allocationK*w^2 := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact hM
    · exact hD
    · exact hG
    · exact hU
    · exact hV
  have hv : ∀ r∈[m,d,g,u,v],r.digits.length≤w := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact record_width_le gapM (divMagnitude x y) w (divMagnitude_bits x y)
    · exact record_width_le gapD (divDenominator x y) w (divDenominator_bits x y)
    · exact record_width_le gapG (divNormalizer x y) w (divNormalizer_bits x y)
    · exact record_width_le gapU (divNumerator x y) w (div_quotient_bits x y).1
    · exact record_width_le gapV (divReducedDenominator x y) w (div_quotient_bits x y).2
  obtain ⟨bankGap,bankWidthBound⟩ := fixed_bank_bounds 5 allocationK [m,d,g,u,v] rfl x y hg hv
  have bankGap' : totalGap [m,d,g,u,v]≤10*allocationK*w^2 := bankGap
  obtain ⟨tr13,run13,len13,_space13⟩ := observe_contract 1 4 oldMemory m [d,g] [v] gapU
    (divNumerator x y) rfl rfl (sign x) [false]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail
  have observedRecordEq : observedRecords [d,g] [v] gapU (divNumerator x y)=[d,g,u,v] := rfl
  rw [observedRecordEq,home_is_header] at run13
  change PSTRTMSeq005.RunsFrom (component (13 : Fin 17)).code
    ⟨observeEntry 1 4 oldMemory,lastCacheTape x y gapM gapD gapG gapU gapV⟩ tr13
    ⟨observePort 1 4 memory,bankHeader x y [m,d,g,u,v]⟩ at run13
  obtain ⟨tr14,run14,len14,_space14⟩ := actual_fifth_allocation 127 memory [m,d,g,u,v] rfl x y hg hv
  rw [allocated_is_work x y m [d,g,u,v] gap] at run14
  change PSTRTMSeq005.RunsFrom (component (14 : Fin 17)).code
    ⟨label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 5 allocationK+1)),bankHeader x y [m,d,g,u,v]⟩ tr14
    ⟨(carryFinal 127 5 allocationK memory (bankWork x y m [d,g,u,v] gap)).q,bankWork x y m [d,g,u,v] gap⟩ at run14
  obtain ⟨tr15,run15,len15,_space15⟩ := cached_ready_contract 127 4 1 0 memory m [d,g,u,v]
    [m,d,g] u [v] [m,d,g,u] v [] rfl rfl rfl rfl rfl
    (PA17TMRatArithmeticPairEncode017.payload (divNumerator x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (divReducedDenominator x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (divNumerator x y)).tail
    (PA17TMRatArithmeticPairEncode017.payload (divReducedDenominator x y)).tail
    (canonical_head_tail _) (canonical_head_tail _) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail gap
  change PSTRTMSeq005.RunsFrom (component (15 : Fin 17)).code
    ⟨label memory (0 : Fin (cachedReadyCap 4 1 0+1)),bankWork x y m [d,g,u,v] gap⟩ tr15
    ⟨label memory (cachedReadyPort 4 1 0 (PA17TMRatArithmeticPairEncode017.payload (divReducedDenominator x y)).head!),
      originalBReady (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail
        (numeratorDigits y).tail (denominatorDigits y).tail m [d,g,u,v] gap
        (PA17TMRatArithmeticPairEncode017.payload (divNumerator x y))
        (PA17TMRatArithmeticPairEncode017.payload (divReducedDenominator x y))⟩ at run15
  rw [original_ready_final_geometry] at run15
  let readyTape := PA17TMRatArithmeticOutputFinish044.pairInput gap
    (PA17TMRatArithmeticOutputFinish044.latestLeft (sign x) (false::(numeratorDigits x).tail)
      (denominatorDigits x).tail (false::(numeratorDigits y).tail) (denominatorDigits y).tail m [d,g,u,v])
    (divNumerator x y) (divReducedDenominator x y)
  have hgap : 3≤gap := by
    have square : 1≤w^2 := by simpa only [one_pow] using Nat.pow_le_pow_left hw 2
    have scaled := Nat.mul_le_mul_left allocationK square
    have constant : 3≤allocationK := by decide
    dsimp only [gap]
    omega
  obtain ⟨tr16,run16,len16,_space16⟩ := dispatch_canonical_contract 4 repairedNegative memory m [d,g,u,v] rfl
    (sign x) (false::(numeratorDigits x).tail) (denominatorDigits x).tail
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail gap hgap
    (divNumerator x y) (divReducedDenominator x y) (x/y)
    (normal_fields x y hd).1 (normal_fields x y hd).2.1 (actual_div_negative x y hd)
  change PSTRTMSeq005.RunsFrom (component (16 : Fin 17)).code
    ⟨dispatchEntry 4 memory,readyTape⟩ tr16
    ⟨dispatchPort 4,Tape.mk₁ (encode [.rational (x/y)])⟩ at run16
  have entry13 : (component (13 : Fin 17)).entry (widen64 oldMemory)=observeEntry 1 4 oldMemory := by
    change observeEntry 1 4 (narrow64 (widen64 oldMemory))=_
    rw [narrow_widen]
  have entry14 : (component (14 : Fin 17)).entry memory=
      label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 5 allocationK+1)) := rfl
  have entry15 : (component (15 : Fin 17)).entry memory=
      label memory (0 : Fin (cachedReadyCap 4 1 0+1)) := rfl
  have entry16 : (component (16 : Fin 17)).entry memory=dispatchEntry 4 memory := rfl
  have seg13 := component_segment (13 : Fin 17) _ _ _ run13
  have seg14 := component_segment (14 : Fin 17) _ _ _ run14
  have seg15 := component_segment (15 : Fin 17) _ _ _ run15
  have seg16 := component_segment (16 : Fin 17) _ _ _ run16
  have decode13 : (component (13 : Fin 17)).decode (observePort 1 4 memory)=memory := zero_decode memory
  have decode14 : (component (14 : Fin 17)).decode
      (carryFinal 127 5 allocationK memory (bankWork x y m [d,g,u,v] gap)).q=memory :=
    allocation128_decode 5 memory _
  have decode15 : (component (15 : Fin 17)).decode
      (label memory (cachedReadyPort 4 1 0 (PA17TMRatArithmeticPairEncode017.payload (divReducedDenominator x y)).head!))=memory :=
    ready_decode memory _
  have step13 := paid_transfer (13 : Fin 17) (by decide) _ run13.2.2.2
  have step14 := paid_transfer (14 : Fin 17) (by decide) _ run14.2.2.2
  have step15 := paid_transfer (15 : Fin 17) (by decide) _ run15.2.2.2
  rw [decode13] at step13
  rw [decode14] at step14
  rw [decode15] at step15
  change TM0.step mulMachine _=some (entryCfg (14 : Fin 17) memory (bankHeader x y [m,d,g,u,v])) at step13
  change TM0.step mulMachine _=some (entryCfg (15 : Fin 17) memory (bankWork x y m [d,g,u,v] gap)) at step14
  change TM0.step mulMachine _=some (entryCfg (16 : Fin 17) memory readyTape) at step15
  have step13' : TM0.step mulMachine (liftCfg (13 : Fin 17)
      ⟨observePort 1 4 memory,bankHeader x y [m,d,g,u,v]⟩)=some (liftCfg (14 : Fin 17)
      ⟨label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 5 allocationK+1)),bankHeader x y [m,d,g,u,v]⟩) := by
    simpa only [entryCfg,entry14] using step13
  have step14' : TM0.step mulMachine (liftCfg (14 : Fin 17)
      ⟨(carryFinal 127 5 allocationK memory (bankWork x y m [d,g,u,v] gap)).q,bankWork x y m [d,g,u,v] gap⟩)=some (liftCfg (15 : Fin 17)
      ⟨label memory (0 : Fin (cachedReadyCap 4 1 0+1)),bankWork x y m [d,g,u,v] gap⟩) := by
    simpa only [entryCfg,entry15] using step14
  have step15' : TM0.step mulMachine (liftCfg (15 : Fin 17)
      ⟨label memory (cachedReadyPort 4 1 0 (PA17TMRatArithmeticPairEncode017.payload (divReducedDenominator x y)).head!),readyTape⟩)=
      some (liftCfg (16 : Fin 17) ⟨dispatchEntry 4 memory,readyTape⟩) := by
    simpa only [entryCfg,entry16] using step15
  have joined1314 := segment_append mulMachine _ _ _ _ _ _ seg13 seg14 step13'
  have joined131415 := segment_append mulMachine _ _ _ _ _ _ joined1314 seg15 step14'
  have joined := segment_append mulMachine _ _ _ _ _ _ joined131415 seg16 step15'
  have globalHalt := final_halt _ run16.2.2.2
  have run := segment_runsFrom mulMachine _ _ _ joined globalHalt
  have vGap : v.gap=gapV := rfl
  have vWidth : v.digits.length≤w :=
    record_width_le gapV (divReducedDenominator x y) w (div_quotient_bits x y).2
  have fee13 := observe_fee_le m [d,g] [v]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
    gapU (divNumerator x y) w n bankGap' bankWidthBound
    (by simpa only [totalGap,Nat.add_zero,vGap,w] using hV)
    (by simpa only [totalWidth,Nat.add_zero] using vWidth)
    (div_quotient_bits x y).1 (by rw [original_source_bankWidth]) hwn hn
  have fee15 := (cached_fees_polynomial allocationK 4 1 0 (by decide) x y m [d,g,u,v]
    [m,d,g] u [v] [m,d,g,u] v [] rfl rfl rfl rfl rfl hg hv
    (divNumerator x y) (divReducedDenominator x y) rfl rfl).2
  have fee16 := output_fee_le m [d,g,u,v]
    (false::(numeratorDigits x).tail) (denominatorDigits x).tail
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail gap
    (divNumerator x y) (divReducedDenominator x y) w n bankGap' bankWidthBound
    (by change bankWidth _ _ _ _≤w;rw [original_source_bankWidth]) (Nat.le_refl _)
    (by rw [PA17TMRatArithmeticPairEncode017.payload_length];exact (div_quotient_bits x y).1)
    (by rw [PA17TMRatArithmeticPairEncode017.payload_length];exact (div_quotient_bits x y).2) hwn hn
  let trace := ((liftTrace (13 : Fin 17) tr13++liftTrace (14 : Fin 17) tr14)++
    liftTrace (15 : Fin 17) tr15)++liftTrace (16 : Fin 17) tr16
  have ht13 : (liftTrace (13 : Fin 17) tr13).length=tr13.length := liftTrace_length (13 : Fin 17) tr13
  have ht14 : (liftTrace (14 : Fin 17) tr14).length=tr14.length := liftTrace_length (14 : Fin 17) tr14
  have ht15 : (liftTrace (15 : Fin 17) tr15).length=tr15.length := liftTrace_length (15 : Fin 17) tr15
  have ht16 : (liftTrace (16 : Fin 17) tr16).length=tr16.length := liftTrace_length (16 : Fin 17) tr16
  have length : trace.length≤finishCoefficient*originalPower x y := by
    simp only [trace,List.length_append]
    rw [ht13,ht14,ht15,ht16]
    have h13 := len13.trans fee13
    have h14 := len14
    have h15 := len15.trans fee15
    have h16 := len16.trans fee16
    change tr13.length≤allocationCoefficient*n^4 at h13
    change tr14.length≤allocationCoefficient*n^4 at h14
    change tr15.length≤feeConstant allocationK*n^4 at h15
    change tr16.length≤allocationCoefficient*n^4 at h16
    change _≤finishCoefficient*n^4
    calc
      _ ≤ ((allocationCoefficient*n^4+allocationCoefficient*n^4)+feeConstant allocationK*n^4)+
          allocationCoefficient*n^4 :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h13 h14) h15) h16
      _ = finishCoefficient*n^4 := by unfold finishCoefficient;ring
  refine ⟨trace,liftCfg (16 : Fin 17) ⟨dispatchPort 4,Tape.mk₁ (encode [.rational (x/y)])⟩,?_,?_,length⟩
  · change PSTRTMSeq005.RunsFrom mulMachine
      (entryCfg (13 : Fin 17) (widen64 oldMemory) (lastCacheTape x y gapM gapD gapG gapU gapV)) trace
      (liftCfg (16 : Fin 17) ⟨dispatchPort 4,Tape.mk₁ (encode [.rational (x/y)])⟩)
    simpa only [entryCfg,entry13,trace] using run
  · exact lift_tape (16 : Fin 17) ⟨dispatchPort 4,Tape.mk₁ (encode [.rational (x/y)])⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivSuffix069
