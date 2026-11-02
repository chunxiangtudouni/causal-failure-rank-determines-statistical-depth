module
public import Structure.PA17_TM_RatArithmetic_MulSuffix_063d
public import Structure.PA17_TM_RatArithmetic_MulPrefix_062a

/-! The same fixed controller actually observes U-zero, allocates its fifth
workspace, loads U/V with all128 carry rows, selects the sign and runs the
complete output/cleanup program to a true global HALT. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulSuffix063

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedOuter043
open PA17TMRatArithmeticMulFields048 PA17TMRatArithmeticWideCache045
open PA17TMRatArithmeticAllocationBounds056 PA17TMRatArithmeticCachedPair054
open PA17TMRatArithmeticNativeTail055 PA17TMRatArithmeticMulClosure059
open PA17TMRatArithmeticMulController057 PA17TMRatArithmeticPairBounds061
open PA17TMRatArithmeticZeroCarry058 PA17TMRatArithmeticSignDispatch053

attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticCachedOuter043.carryCap PA17TMRatArithmeticCachedPair054.cachedReadyCap
  PA17TMRatArithmeticZeroCarry058.observeCap PA17TMRatArithmeticSignDispatch053.dispatchCap

def finishCoefficient : Nat := 3*allocationCoefficient+feeConstant allocationK

theorem finish_segment (x y : Rat) (gapM gapD gapG gapU gapV : Nat)
    (hM : gapM≤2*allocationK*(fieldWidth x y)^2)
    (hD : gapD≤2*allocationK*(fieldWidth x y)^2)
    (hG : gapG≤2*allocationK*(fieldWidth x y)^2)
    (hU : gapU≤2*allocationK*(fieldWidth x y)^2)
    (hV : gapV≤2*allocationK*(fieldWidth x y)^2) :
    ∃ trace last, PSTRTMSeq005.RunsFrom mulMachine
        (entryCfg (13 : Fin 17) (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y))
          (lastCacheTape x y gapM gapD gapG gapU gapV)) trace last ∧
      last.Tape=Tape.mk₁ (encode [.rational (x*y)]) ∧
      trace.length≤finishCoefficient*originalPower x y := by
  let m := mRecord x y gapM
  let d := dRecord x y gapD
  let g := gRecord x y gapG
  let u := uRecord x y gapU
  let v := vRecord x y gapV
  let oldMemory := PA17TMRatArithmeticMulStart049.actualMemory x y
  let memory := observedMemory oldMemory (decide (quotientNumerator x y=0))
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
    · exact record_width_le gapM (productMagnitude x y) w (productMagnitude_bits x y)
    · exact record_width_le gapD (productDenominator x y) w (productDenominator_bits x y)
    · exact record_width_le gapG (normalizer x y) w (normalizer_bits x y)
    · exact record_width_le gapU (quotientNumerator x y) w (normalized_bits x y).1
    · exact record_width_le gapV (quotientDenominator x y) w (normalized_bits x y).2
  obtain ⟨bankGap,bankWidthBound⟩ := fixed_bank_bounds 5 allocationK [m,d,g,u,v] rfl x y hg hv
  have bankGap' : totalGap [m,d,g,u,v]≤10*allocationK*w^2 := bankGap
  obtain ⟨tr13,run13,len13,_space13⟩ := observe_contract 1 4 oldMemory m [d,g] [v] gapU
    (quotientNumerator x y) rfl rfl (sign x) [false]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail
  have zeroHeader := zero_output_is_header x y m d g u v rfl
  have uGap : u.gap=gapU := rfl
  rw [uGap] at zeroHeader
  rw [zeroHeader] at run13
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
    (PA17TMRatArithmeticPairEncode017.payload (quotientNumerator x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (quotientNumerator x y)).tail
    (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator x y)).tail
    (canonical_head_tail _) (canonical_head_tail _) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail gap
  change PSTRTMSeq005.RunsFrom (component (15 : Fin 17)).code
    ⟨label memory (0 : Fin (cachedReadyCap 4 1 0+1)),bankWork x y m [d,g,u,v] gap⟩ tr15
    ⟨label memory (cachedReadyPort 4 1 0 (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator x y)).head!),
      originalBReady (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail
        (numeratorDigits y).tail (denominatorDigits y).tail m [d,g,u,v] gap
        (PA17TMRatArithmeticPairEncode017.payload (quotientNumerator x y))
        (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator x y))⟩ at run15
  rw [original_ready_final_geometry] at run15
  let readyTape := PA17TMRatArithmeticOutputFinish044.pairInput gap
    (PA17TMRatArithmeticOutputFinish044.latestLeft (sign x) (false::(numeratorDigits x).tail)
      (denominatorDigits x).tail (false::(numeratorDigits y).tail) (denominatorDigits y).tail m [d,g,u,v])
    (quotientNumerator x y) (quotientDenominator x y)
  have hgap : 3≤gap := by
    have square : 1≤w^2 := by simpa only [one_pow] using Nat.pow_le_pow_left hw 2
    have scaled := Nat.mul_le_mul_left allocationK square
    have constant : 3≤allocationK := by decide
    dsimp only [gap]
    omega
  obtain ⟨tr16,run16,len16,_space16⟩ := dispatch_canonical_contract 4 repairedNegative memory m [d,g,u,v] rfl
    (sign x) (false::(numeratorDigits x).tail) (denominatorDigits x).tail
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail gap hgap
    (quotientNumerator x y) (quotientDenominator x y) (x*y)
    (pipeline_fields x y).1 (pipeline_fields x y).2.1 (actual_product_negative x y)
  change PSTRTMSeq005.RunsFrom (component (16 : Fin 17)).code
    ⟨dispatchEntry 4 memory,readyTape⟩ tr16
    ⟨dispatchPort 4,Tape.mk₁ (encode [.rational (x*y)])⟩ at run16
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
      (label memory (cachedReadyPort 4 1 0 (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator x y)).head!))=memory :=
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
      ⟨label memory (cachedReadyPort 4 1 0 (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator x y)).head!),readyTape⟩)=
      some (liftCfg (16 : Fin 17) ⟨dispatchEntry 4 memory,readyTape⟩) := by
    simpa only [entryCfg,entry16] using step15
  have joined1314 := segment_append mulMachine _ _ _ _ _ _ seg13 seg14 step13'
  have joined131415 := segment_append mulMachine _ _ _ _ _ _ joined1314 seg15 step14'
  have joined := segment_append mulMachine _ _ _ _ _ _ joined131415 seg16 step15'
  have globalHalt := final_halt _ run16.2.2.2
  have run := segment_runsFrom mulMachine _ _ _ joined globalHalt
  have vGap : v.gap=gapV := rfl
  have vWidth : v.digits.length≤w :=
    record_width_le gapV (quotientDenominator x y) w (normalized_bits x y).2
  have fee13 := observe_fee_le m [d,g] [v]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
    gapU (quotientNumerator x y) w n bankGap' bankWidthBound
    (by simpa only [totalGap,Nat.add_zero,vGap,w] using hV)
    (by simpa only [totalWidth,Nat.add_zero] using vWidth)
    (normalized_bits x y).1 (by rw [original_source_bankWidth]) hwn hn
  have fee15 := (cached_fees_polynomial allocationK 4 1 0 (by decide) x y m [d,g,u,v]
    [m,d,g] u [v] [m,d,g,u] v [] rfl rfl rfl rfl rfl hg hv
    (quotientNumerator x y) (quotientDenominator x y) rfl rfl).2
  have fee16 := output_fee_le m [d,g,u,v]
    (false::(numeratorDigits x).tail) (denominatorDigits x).tail
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail gap
    (quotientNumerator x y) (quotientDenominator x y) w n bankGap' bankWidthBound
    (by change bankWidth _ _ _ _≤w;rw [original_source_bankWidth]) (Nat.le_refl _)
    (by rw [PA17TMRatArithmeticPairEncode017.payload_length];exact (normalized_bits x y).1)
    (by rw [PA17TMRatArithmeticPairEncode017.payload_length];exact (normalized_bits x y).2) hwn hn
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
  refine ⟨trace,liftCfg (16 : Fin 17) ⟨dispatchPort 4,Tape.mk₁ (encode [.rational (x*y)])⟩,?_,?_,length⟩
  · change PSTRTMSeq005.RunsFrom mulMachine
      (entryCfg (13 : Fin 17) (widen64 oldMemory) (lastCacheTape x y gapM gapD gapG gapU gapV)) trace
      (liftCfg (16 : Fin 17) ⟨dispatchPort 4,Tape.mk₁ (encode [.rational (x*y)])⟩)
    simpa only [entryCfg,entry13,trace] using run
  · exact lift_tape (16 : Fin 17) ⟨dispatchPort 4,Tape.mk₁ (encode [.rational (x*y)])⟩

open PA17TMRatArithmeticMulPrefix062

def mulTimeCoefficient : Nat := prefixCoefficient+2*roundCoefficient+finishCoefficient

def mulResourceCoefficient : Nat := 2*mulTimeCoefficient+2

theorem mulResourceCoefficient_pos : 0<mulResourceCoefficient := by
  unfold mulResourceCoefficient
  omega

/-- All seventeen local executions are physically concatenated, including
every inter-component write-self transition. The final eval membership
comes from that actual chain and HALT. No local-run oracle is a premise. -/
theorem original_mul_runs (x y : Rat) :
    ∃ trace final, Runs mulMachine (encode [.rational x,.rational y]) trace final ∧
      final.Tape=Tape.mk₁ (encode [.rational (x*y)]) ∧
      trace.length≤mulTimeCoefficient*originalPower x y := by
  obtain ⟨gapM,gapD,gapG,tp,lastP,_lowerM,upperM,_lowerD,upperD,_lowerG,upperG,segP,stepP,lenP⟩ :=
    mdg_segment x y
  obtain ⟨gapU,tu,lastU,_lowerU,upperU,segU,stepU,lenU⟩ := u_segment x y
    (PA17TMRatArithmeticMulStart049.actualMemory x y) gapM gapD gapG upperM upperD upperG
  obtain ⟨gapV,tv,lastV,_lowerV,upperV,segV,stepV,lenV⟩ := v_segment x y
    (PA17TMRatArithmeticMulStart049.actualMemory x y) gapM gapD gapG gapU upperM upperD upperG upperU
  obtain ⟨tf,final,runF,whole,lenF⟩ := finish_segment x y gapM gapD gapG gapU gapV
    upperM upperD upperG upperU upperV
  have joinedPU := segment_append mulMachine _ lastP _ lastU tp tu segP segU stepP
  have joinedPUV := segment_append mulMachine _ lastU _ lastV _ tv joinedPU segV stepU
  have segF : Segment mulMachine _ tf final := ⟨runF.1,runF.2.1,runF.2.2.1⟩
  have joined := segment_append mulMachine _ lastV _ final _ tf joinedPUV segF stepV
  let trace := ((tp++tu)++tv)++tf
  have actual : Runs mulMachine (encode [.rational x,.rational y]) trace final :=
    PSTRTMTrace002.runs_of_chain mulMachine _ _ _ joined.1 joined.2.1 joined.2.2 runF.2.2.2
  have length : trace.length≤mulTimeCoefficient*originalPower x y := by
    simp only [trace,List.length_append]
    change tp.length≤prefixCoefficient*originalPower x y at lenP
    calc
      _ ≤ ((prefixCoefficient*originalPower x y+roundCoefficient*originalPower x y)+
          roundCoefficient*originalPower x y)+finishCoefficient*originalPower x y :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add lenP lenU) lenV) lenF
      _ = mulTimeCoefficient*originalPower x y := by unfold mulTimeCoefficient;ring
  exact ⟨trace,final,actual,whole,length⟩

/-- Time and EVERY visited-space prefix refer to this same actual run
from the exact two-Rat codec, including all allocation/native/cleanup. -/
theorem original_mul_contract (x y : Rat) :
    ∃ trace final, Runs mulMachine (encode [.rational x,.rational y]) trace final ∧
      final.Tape=Tape.mk₁ (encode [.rational (x*y)]) ∧
      trace.length≤mulResourceCoefficient*originalPower x y ∧
      ∀ prefixLength, visitedSpace mulMachine (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤mulResourceCoefficient*originalPower x y := by
  obtain ⟨trace,final,actual,whole,time⟩ := original_mul_runs x y
  let i := (encode [.rational x,.rational y]).length
  have input : i+1≤(i+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : (1 : Nat) ≤ i + 1) (by decide : (1 : Nat)≤4)
  have hc : mulTimeCoefficient≤mulResourceCoefficient := by unfold mulResourceCoefficient;omega
  refine ⟨trace,final,actual,whole,time.trans (Nat.mul_le_mul_right _ hc),?_⟩
  intro prefixLength
  have space := PSTRTMTrace002.visitedSpace_le mulMachine i (trace.take prefixLength)
  have taken : (trace.take prefixLength).length≤trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  change trace.length≤mulTimeCoefficient*(i+1)^4 at time
  change visitedSpace mulMachine i (trace.take prefixLength)≤mulResourceCoefficient*(i+1)^4
  calc
    _ ≤ i+2*(trace.take prefixLength).length+1 := space
    _ ≤ i+2*(mulTimeCoefficient*(i+1)^4)+1 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (taken.trans time)) i) 1
    _ = (i+1)+2*(mulTimeCoefficient*(i+1)^4) := by ac_rfl
    _ ≤ (i+1)^4+2*(mulTimeCoefficient*(i+1)^4) := Nat.add_le_add_right input _
    _ = (2*mulTimeCoefficient+1)*(i+1)^4 := by ring
    _ ≤ mulResourceCoefficient*(i+1)^4 :=
      Nat.mul_le_mul_right _ (by unfold mulResourceCoefficient;omega)

theorem original_mul_computes (x y : Rat) :
    computes mulMachine (encode [.rational x,.rational y]) (encode [.rational (x*y)])
      (mulResourceCoefficient*originalPower x y) (mulResourceCoefficient*originalPower x y) := by
  obtain ⟨trace,final,actual,whole,time,space⟩ := original_mul_contract x y
  refine ⟨trace,final,actual,?_,time,?_⟩
  · rw [whole]
    exact Turing.Tape.mk'_right₀ _ _
  · have h := space trace.length
    simpa only [List.take_length] using h

/-- The fixed finite program and positive c,d precede ALL original Rat
operands. There are no room, signs, zero flags, widths, counts or fuel inputs. -/
theorem original_mul_exists :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ trace final,
        Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=Tape.mk₁ (encode [.rational (x*y)]) ∧
        trace.length≤c*((encode [.rational x,.rational y]).length+1)^d ∧
        ∀ prefixLength, visitedSpace program (encode [.rational x,.rational y]).length
          (trace.take prefixLength)≤c*((encode [.rational x,.rational y]).length+1)^d := by
  refine ⟨controllerCap,mulResourceCoefficient,4,mulMachine,mulResourceCoefficient_pos,by decide,?_⟩
  intro x y
  exact original_mul_contract x y

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulSuffix063
