module
public import Structure.PA17_TM_RatArithmetic_MulClosure_059b
public import Structure.PA17_TM_RatArithmetic_PairBounds_061a
public import Structure.PA17_TM_RatArithmetic_MulController_057a

/-! The actual U division in phases7..9 of the one fixed controller.
The incoming M,D,G records were physically produced by phases0..6.
The final transfer is an actual TM step, ready for the actual V allocator. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulSuffix063

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedOuter043
open PA17TMRatArithmeticMulFields048 PA17TMRatArithmeticWideCache045
open PA17TMRatArithmeticAllocationBounds056 PA17TMRatArithmeticCachedPair054
open PA17TMRatArithmeticNativeTail055 PA17TMRatArithmeticMulClosure059
open PA17TMRatArithmeticMulController057 PA17TMRatArithmeticPairBounds061

attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticCachedOuter043.carryCap
  PA17TMRatArithmeticCachedPair054.cachedPairCap
  PA17TMRatArithmeticNativeTail055.carriedTailCap PA17TMRatArithmeticNativeTail055.tailCap

def originalPower (x y : Rat) : Nat := ((encode [.rational x,.rational y]).length+1)^4

def roundCoefficient : Nat := allocationCoefficient+feeConstant allocationK+nativeCoefficient

def mRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (productMagnitude x y)
def dRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (productDenominator x y)
def gRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (normalizer x y)
def uRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (quotientNumerator x y)
def vRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (quotientDenominator x y)

theorem record_payload_length (gap value : Nat) : (resultRecord gap value).digits.length=natBits value := by
  simp only [resultRecord,PSTRTMNatValue017.rawPayload,List.length_ofFn]

theorem record_width_le (gap value width : Nat) (h : natBits value≤width) :
    (resultRecord gap value).digits.length≤width := by
  rw [record_payload_length]
  exact h

theorem original_source_bankWidth (x y : Rat) :
    bankWidth (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)=fieldWidth x y :=
  originalWidth_eq x y

/-- Internal produced-record invariants. There is no eligibility condition
on the original x/y, nor an answer, width, count or observed bit input. -/
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
    · exact record_width_le gapM (productMagnitude x y) w (productMagnitude_bits x y)
    · exact record_width_le gapD (productDenominator x y) w (productDenominator_bits x y)
    · exact record_width_le gapG (normalizer x y) w (normalizer_bits x y)
  obtain ⟨tr7,run7,len7,_space7⟩ := actual_allocation_contract 63 3 memory [m,d,g] rfl (by decide) x y hg hv
  rw [allocated_is_work x y m [d,g] gap] at run7
  change PSTRTMSeq005.RunsFrom (component (7 : Fin 17)).code
    ⟨label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 3 allocationK+1)),bankHeader x y [m,d,g]⟩ tr7
    ⟨(carryFinal 63 3 allocationK memory (bankWork x y m [d,g] gap)).q,bankWork x y m [d,g] gap⟩ at run7
  obtain ⟨tr8,run8,len8,_space8⟩ := cached_pair_contract 63 2 2 0 memory m [d,g] [] m [d,g] [m,d] g []
    rfl rfl rfl rfl rfl
    (PA17TMRatArithmeticPairEncode017.payload (productMagnitude x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (normalizer x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (productMagnitude x y)).tail
    (PA17TMRatArithmeticPairEncode017.payload (normalizer x y)).tail
    (canonical_head_tail _) (canonical_head_tail _) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    gap (productMagnitude x y) (normalizer x y) rfl rfl
  change PSTRTMSeq005.RunsFrom (component (8 : Fin 17)).code
    ⟨label memory (0 : Fin (cachedPairCap 2 2 0+1)),bankWork x y m [d,g] gap⟩ tr8
    ⟨label memory (cachedPairPort 2 2 0),bankNative x y m [d,g] gap (productMagnitude x y) (normalizer x y)⟩ at run8
  have actual := quotient_allocated_runsFrom (productMagnitude x y) (normalizer x y) w
    (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [d,g]) hw (five_scales x y).2.2.2.1
  obtain ⟨gapU,tr9,lower,upper,run9,len9,_space9⟩ := carriedTail_contract 63 PA17TMDivisionFull012.quotientMachine
    2 memory m [d,g] rfl (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail gap
    (productMagnitude x y) (normalizer x y) (quotientNumerator x y) actual
  rw [←native_is_tail_input,tail_output_is_header] at run9
  change PSTRTMSeq005.RunsFrom (component (9 : Fin 17)).code
    ⟨carriedTailEntry 63 1136 2 memory,bankNative x y m [d,g] gap (productMagnitude x y) (normalizer x y)⟩ tr9
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
    (bankNative x y m [d,g] gap (productMagnitude x y) (normalizer x y))) at step8
  change TM0.step mulMachine _=some (entryCfg (10 : Fin 17) (widen64 memory)
    (bankHeader x y [m,d,g,uRecord x y gapU])) at step9
  have step7' : TM0.step mulMachine (liftCfg (7 : Fin 17)
      ⟨(carryFinal 63 3 allocationK memory (bankWork x y m [d,g] gap)).q,bankWork x y m [d,g] gap⟩)=some (liftCfg (8 : Fin 17)
      ⟨label memory (0 : Fin (cachedPairCap 2 2 0+1)),bankWork x y m [d,g] gap⟩) := by
    simpa only [entryCfg,entry8] using step7
  have step8' : TM0.step mulMachine (liftCfg (8 : Fin 17)
      ⟨label memory (cachedPairPort 2 2 0),bankNative x y m [d,g] gap (productMagnitude x y) (normalizer x y)⟩)=some (liftCfg (9 : Fin 17)
      ⟨carriedTailEntry 63 1136 2 memory,bankNative x y m [d,g] gap (productMagnitude x y) (normalizer x y)⟩) := by
    simpa only [entryCfg,entry9] using step8
  have joined78 := segment_append mulMachine _ _ _ _ _ _ seg7 seg8 step7'
  have joined := segment_append mulMachine _ _ _ _ _ _ joined78 seg9 step8'
  obtain ⟨bankGap,bankWidthBound⟩ := cache_totals_le 3 [m,d,g] rfl (by decide) x y hg hv
  have fee8 := (cached_fees_polynomial allocationK 2 2 0 (by decide) x y m [d,g] [] m [d,g] [m,d] g []
    rfl rfl rfl rfl rfl hg hv (productMagnitude x y) (normalizer x y) rfl rfl).1
  have fee9 := native_tail_fee_le 2 (by decide) m [d,g]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
    gapU (productMagnitude x y) (normalizer x y) (quotientNumerator x y) w n
    bankGap bankWidthBound gapUbound (five_scales x y).2.2.2.1 (normalized_bits x y).1
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


open PA17TMRatArithmeticReturnHome037

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
    · exact record_width_le gapM (productMagnitude x y) w (productMagnitude_bits x y)
    · exact record_width_le gapD (productDenominator x y) w (productDenominator_bits x y)
    · exact record_width_le gapG (normalizer x y) w (normalizer_bits x y)
    · exact record_width_le gapU (quotientNumerator x y) w (normalized_bits x y).1
  obtain ⟨tr10,run10,len10,_space10⟩ := actual_allocation_contract 63 4 memory [m,d,g,u] rfl (by decide) x y hg hv
  rw [allocated_is_work x y m [d,g,u] gap] at run10
  change PSTRTMSeq005.RunsFrom (component (10 : Fin 17)).code
    ⟨label memory (0 : Fin (PA17TMRatArithmeticCachedOuter043.outerCap 4 allocationK+1)),bankHeader x y [m,d,g,u]⟩ tr10
    ⟨(carryFinal 63 4 allocationK memory (bankWork x y m [d,g,u] gap)).q,bankWork x y m [d,g,u] gap⟩ at run10
  obtain ⟨tr11,run11,len11,_space11⟩ := cached_pair_contract 63 3 2 1 memory m [d,g,u] [m] d [g,u] [m,d] g [u]
    rfl rfl rfl rfl rfl
    (PA17TMRatArithmeticPairEncode017.payload (productDenominator x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (normalizer x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (productDenominator x y)).tail
    (PA17TMRatArithmeticPairEncode017.payload (normalizer x y)).tail
    (canonical_head_tail _) (canonical_head_tail _) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    gap (productDenominator x y) (normalizer x y) rfl rfl
  change PSTRTMSeq005.RunsFrom (component (11 : Fin 17)).code
    ⟨label memory (0 : Fin (cachedPairCap 3 2 1+1)),bankWork x y m [d,g,u] gap⟩ tr11
    ⟨label memory (cachedPairPort 3 2 1),bankNative x y m [d,g,u] gap (productDenominator x y) (normalizer x y)⟩ at run11
  have actual := quotient_allocated_runsFrom (productDenominator x y) (normalizer x y) w
    (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [d,g,u]) hw (five_scales x y).2.2.2.2
  obtain ⟨gapV,trLocal,lastLocal,runLocal,lastTape,lower,upper,lenLocal,_spaceLocal⟩ := actual
  let output := lastCacheTape x y gapM gapD gapG gapU gapV
  have lastTape' : lastLocal.Tape=output :=
    lastTape.trans (newRecord_home (sign x) [false] (false::(numeratorDigits x).tail)
      (false::(denominatorDigits x).tail) (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
      m [d,g,u] gapV (quotientDenominator x y))
  have lastEq : lastLocal=⟨lastLocal.q,output⟩ := by
    cases lastLocal with
    | mk q tape => exact congrArg (fun t => (⟨q,t⟩ : MachineState 1170)) lastTape'
  change PSTRTMSeq005.RunsFrom PA17TMRatArithmeticNativeCache030.quotientCacheMachine
    ⟨0,tailInput (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [d,g,u]
      gap (productDenominator x y) (normalizer x y)⟩ trLocal lastLocal at runLocal
  rw [←native_is_tail_input,lastEq] at runLocal
  have run12 := quotient_record_runs memory _ _ _ runLocal
  let tr12 := trLocal.map (blockCfg (s:=1170) memory)
  change PSTRTMSeq005.RunsFrom (component (12 : Fin 17)).code
    ⟨label memory (0 : Fin 1171),bankNative x y m [d,g,u] gap (productDenominator x y) (normalizer x y)⟩ tr12
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
    (bankNative x y m [d,g,u] gap (productDenominator x y) (normalizer x y))) at step11
  change TM0.step mulMachine _=some (entryCfg (13 : Fin 17) (widen64 memory) output) at step12
  have step10' : TM0.step mulMachine (liftCfg (10 : Fin 17)
      ⟨(carryFinal 63 4 allocationK memory (bankWork x y m [d,g,u] gap)).q,bankWork x y m [d,g,u] gap⟩)=some (liftCfg (11 : Fin 17)
      ⟨label memory (0 : Fin (cachedPairCap 3 2 1+1)),bankWork x y m [d,g,u] gap⟩) := by
    simpa only [entryCfg,entry11] using step10
  have step11' : TM0.step mulMachine (liftCfg (11 : Fin 17)
      ⟨label memory (cachedPairPort 3 2 1),bankNative x y m [d,g,u] gap (productDenominator x y) (normalizer x y)⟩)=some (liftCfg (12 : Fin 17)
      ⟨label memory (0 : Fin 1171),bankNative x y m [d,g,u] gap (productDenominator x y) (normalizer x y)⟩) := by
    simpa only [entryCfg,entry12] using step11
  have joined1011 := segment_append mulMachine _ _ _ _ _ _ seg10 seg11 step10'
  have joined := segment_append mulMachine _ _ _ _ _ _ joined1011 seg12 step11'
  have fee11 := (cached_fees_polynomial allocationK 3 2 1 (by decide) x y m [d,g,u] [m] d [g,u] [m,d] g [u]
    rfl rfl rfl rfl rfl hg hv (productDenominator x y) (normalizer x y) rfl rfl).1
  have fee12 := native_v_fee_le (productDenominator x y) (normalizer x y) w n
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

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulSuffix063
