module
public import Structure.PA17_TM_RatArithmetic_MulController_057a
public import Structure.PA17_TM_RatArithmetic_MulClosure_059b
public import Structure.PA17_TM_RatArithmetic_PairBounds_061a

/-! The original raw-input prefix of the SAME fixed seventeen-phase
controller. Only real local runs and paid transitions are concatenated.
The final boundary is phase6's actual local HALT, with its real step into
phase7 stated separately; no phase7 singleton is duplicated. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulPrefix062

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticMulController057 PA17TMRatArithmeticMulClosure059
open PA17TMRatArithmeticMulFields048 PA17TMRatArithmeticMulStart049
open PA17TMRatArithmeticAllocationBounds056 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeCache030
open PA17TMRatArithmeticCachedPair054 PA17TMRatArithmeticPairBounds061
attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticMulController057.controllerCap
  PA17TMRatArithmeticCachedPair054.originalPairCap PA17TMRatArithmeticCachedPair054.originalReadyCap
  PA17TMRatArithmeticCachedPair054.originalFirstCap
  PA17TMRatArithmeticCachedPair054.cachedPairCap PA17TMRatArithmeticCachedPair054.cachedReadyCap
  PA17TMRatArithmeticCachedPair054.cachedFirstCap
  PA17TMRatArithmeticNativeTail055.carriedTailCap PA17TMRatArithmeticNativeTail055.tailCap

def recordM (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (productMagnitude x y)
def recordD (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (productDenominator x y)
def recordG (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (normalizer x y)
def freshGap (x y : Rat) : Nat := allocationK*(fieldWidth x y)^2
def inputPower (x y : Rat) : Nat := ((encode [.rational x,.rational y]).length+1)^4

def denFinal (x y : Rat) (gapM : Nat) : MachineState (component (2 : Fin 17)).states :=
  ⟨label (actualMemory x y) (originalPairPort 0),
    bankNative x y (recordM x y gapM) [] (freshGap x y) x.den y.den⟩

def gcdFinal (x y : Rat) (gapM gapD gapG : Nat) : MachineState (component (6 : Fin 17)).states :=
  ⟨carriedTailPort 63 3564 1 (actualMemory x y),
    bankHeader x y [recordM x y gapM,recordD x y gapD,recordG x y gapG]⟩

private theorem row_entry_cfg (states : Nat) (code : Machine (totalStates 63 states))
    (memory : Fin 64) (tape : Tape Bool) :
    (⟨(row64Component states code).entry (widen64 memory),tape⟩ : MachineState (totalStates 63 states))=
      blockCfg memory (⟨0,tape⟩ : MachineState states) := by
  rw [row64_entry]
  rfl

private theorem transfer_to (phase next : Fin 17) (h : phase.val<16) (hnext : nextPhase phase=next)
    (last : MachineState (component phase).states) (memory : Fin 128) (tape : Tape Bool)
    (halt : TM0.step (component phase).code last=none)
    (decode : (component phase).decode last.q=memory) (whole : last.Tape=tape) :
    TM0.step mulMachine (liftCfg phase last)=some (entryCfg next memory tape) := by
  rw [paid_transfer phase h last halt,hnext,decode,whole]

private theorem recordM_width (x y : Rat) (gap : Nat) : (recordM x y gap).digits.length≤fieldWidth x y := by
  simpa only [recordM,resultRecord,PSTRTMNatValue017.rawPayload,List.length_ofFn] using productMagnitude_bits x y

private theorem recordD_width (x y : Rat) (gap : Nat) : (recordD x y gap).digits.length≤fieldWidth x y := by
  simpa only [recordD,resultRecord,PSTRTMNatValue017.rawPayload,List.length_ofFn] using productDenominator_bits x y

private theorem first_chunk (x y : Rat) :
    ∃ gapM trace, 6≤gapM ∧ gapM≤2*allocationK*(fieldWidth x y)^2 ∧
      Segment mulMachine (TM0.init (encode [.rational x,.rational y])) trace
        (liftCfg (2 : Fin 17) (denFinal x y gapM)) ∧
      TM0.step mulMachine (liftCfg (2 : Fin 17) (denFinal x y gapM))=
        some (entryCfg (3 : Fin 17) (widen64 (actualMemory x y))
          (bankNative x y (recordM x y gapM) [] (freshGap x y) x.den y.den)) ∧
      trace.length≤(PA17TMRatArithmeticFirstRaw052.firstTimeC+allocationCoefficient+feeConstant allocationK)*inputPower x y := by
  let memory := actualMemory x y
  obtain ⟨gapM,t0,lower,upper,r0,l0⟩ := PA17TMRatArithmeticFirstRaw052.original_first_mul_runs x y
  let m := recordM x y gapM
  have hg : ∀ r∈[m],r.gap≤2*allocationK*(fieldWidth x y)^2 := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact upper
  have hv : ∀ r∈[m],r.digits.length≤fieldWidth x y := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact recordM_width x y gapM
  obtain ⟨t1,r1,l1,_s1⟩ := actual_allocation_contract 63 1 memory [m] rfl (by decide) x y hg hv
  obtain ⟨t2,r2,l2,_s2⟩ := denominator_contract 63 0 memory x y (actualMemory_retains_old x y) [false] m [] rfl (freshGap x y)
  have fee2 := original_fee_polynomial allocationK 0 (by decide) memory.val x y m [] rfl hg hv
  have start1 : (⟨(component (1 : Fin 17)).entry (widen64 memory),bankHeader x y [m]⟩ :
      MachineState (component (1 : Fin 17)).states)=
      PA17TMRatArithmeticCachedOuter043.carryEntry 63 1 allocationK memory (bankHeader x y [m]) :=
    row_entry_cfg _ (PA17TMRatArithmeticCachedOuter043.carryMachine 63 1 allocationK) memory _
  have start2 : (⟨(component (2 : Fin 17)).entry (widen64 memory),bankWork x y m [] (freshGap x y)⟩ :
      MachineState (component (2 : Fin 17)).states)=
      blockCfg memory (⟨0,denominatorInput x y [false] m [] (freshGap x y)⟩ : MachineState (originalPairCap 0)) :=
    row_entry_cfg _ (originalPairMachine 63 .dx .dy 0) memory _
  let end0 : MachineState (component (0 : Fin 17)).states := PA17TMRatArithmeticFirstRaw052.firstFinal x y gapM
  let end1 : MachineState (component (1 : Fin 17)).states :=
    PA17TMRatArithmeticCachedOuter043.carryFinal 63 1 allocationK memory (bankWork x y m [] (freshGap x y))
  have r0From : PSTRTMSeq005.RunsFrom PA17TMRatArithmeticFirstRaw052.firstMachine
      (TM0.init (encode [.rational x,.rational y])) t0 (PA17TMRatArithmeticFirstRaw052.firstFinal x y gapM) :=
    ⟨r0.1,r0.2.1,r0.2.2.1,r0.2.2.2.1⟩
  change PSTRTMSeq005.RunsFrom (component (0 : Fin 17)).code
    (TM0.init (encode [.rational x,.rational y])) t0 end0 at r0From
  have tape0 : end0.Tape=bankHeader x y [m] := by
    exact (PA17TMRatArithmeticFirstRaw052.firstFinal_tape x y gapM).trans (first_is_header x y gapM)
  have decode0 : (component (0 : Fin 17)).decode end0.q=widen64 memory :=
    first_decode memory (PA17TMRatArithmeticFirstMul051.firstCycleOutput x y [false] gapM)
  have step0 := transfer_to 0 1 (by decide) (by decide) end0 (widen64 memory) _ r0From.2.2.2 decode0 tape0
  rw [allocated_is_work] at r1
  change PSTRTMSeq005.RunsFrom (component (1 : Fin 17)).code
    (PA17TMRatArithmeticCachedOuter043.carryEntry 63 1 allocationK memory (bankHeader x y [m])) t1 end1 at r1
  rw [←start1] at r1
  have decode1 : (component (1 : Fin 17)).decode end1.q=widen64 memory := allocation64_decode 1 memory _
  have step1 := transfer_to 1 2 (by decide) (by decide) end1 (widen64 memory) _ r1.2.2.2 decode1 rfl
  rw [←start2] at r2
  change PSTRTMSeq005.RunsFrom (component (2 : Fin 17)).code _ t2 (denFinal x y gapM) at r2
  have decode2 : (component (2 : Fin 17)).decode (denFinal x y gapM).q=widen64 memory := denominator_decode memory
  have step2 := transfer_to 2 3 (by decide) (by decide) (denFinal x y gapM) (widen64 memory) _ r2.2.2.2 decode2 rfl
  have sg0 := component_segment 0 _ _ _ r0From
  rw [initial_mapped] at sg0
  have sg1 := component_segment 1 _ _ _ r1
  have sg2 := component_segment 2 _ _ _ r2
  have sg01 := segment_append mulMachine _ _ _ _ _ _ sg0 sg1 step0
  have sg012 := segment_append mulMachine _ _ _ _ _ _ sg01 sg2 step1
  refine ⟨gapM,(liftTrace 0 t0++liftTrace 1 t1)++liftTrace 2 t2,lower,upper,sg012,step2,?_⟩
  simp only [List.length_append]
  rw [liftTrace_length (0 : Fin 17) t0,liftTrace_length (1 : Fin 17) t1,liftTrace_length (2 : Fin 17) t2]
  have lt2 := l2.trans fee2
  change t0.length≤PA17TMRatArithmeticFirstRaw052.firstTimeC*inputPower x y at l0
  change t1.length≤allocationCoefficient*inputPower x y at l1
  change t2.length≤feeConstant allocationK*inputPower x y at lt2
  calc
    _ ≤ PA17TMRatArithmeticFirstRaw052.firstTimeC*inputPower x y+
        allocationCoefficient*inputPower x y+feeConstant allocationK*inputPower x y :=
      Nat.add_le_add (Nat.add_le_add l0 l1) lt2
    _ = _ := by ring

private theorem native_stage {states : Nat} (native : Machine states) (j : Nat) (hj : j≤3)
    (x y : Rat) (first : RecordSpec) (later : List RecordSpec) (hlen : later.length=j) (a b value : Nat)
    (hg : ∀ r∈first::later,r.gap≤2*allocationK*(fieldWidth x y)^2)
    (hv : ∀ r∈first::later,r.digits.length≤fieldWidth x y)
    (size : scale a b≤4*fieldWidth x y) (width : natBits value≤fieldWidth x y)
    (actual : WideCacheResult native a b value
      (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
        (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) first later) (freshGap x y)) :
    ∃ gap trace, 6≤gap ∧ gap≤2*allocationK*(fieldWidth x y)^2 ∧
      PSTRTMSeq005.RunsFrom (carriedTailMachine 63 native j)
        ⟨carriedTailEntry 63 states j (actualMemory x y),bankNative x y first later (freshGap x y) a b⟩ trace
        ⟨carriedTailPort 63 states j (actualMemory x y),bankHeader x y (first::(later++[resultRecord gap value]))⟩ ∧
      trace.length≤nativeCoefficient*inputPower x y := by
  obtain ⟨gap,trace,lower,upper,run,time,_space⟩ := carriedTail_contract 63 native j (actualMemory x y)
    first later hlen (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail (freshGap x y) a b value actual
  have hw : 1≤fieldWidth x y := by have h := fieldWidth_ge_four x y; omega
  have gapBound := new_gap_bound a b (fieldWidth x y) gap hw size upper
  have hn : (first::later).length=j+1 := by simp only [List.length_cons,hlen]
  obtain ⟨totalG,totalV⟩ := cache_totals_le (j+1) (first::later) hn (by omega) x y hg hv
  have hsource : bankWidth (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)≤fieldWidth x y := by
    change PA17TMRatArithmeticFarLoad031.bankWidth (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail≤_
    exact (PA17TMRatArithmeticPairInput050.original_source_width x y).le
  have bound := native_tail_fee_le j hj first later (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) gap a b value (fieldWidth x y)
    ((encode [.rational x,.rational y]).length+1) totalG totalV gapBound size width hsource
    (by have h := original_width_le_input x y; omega) (by omega)
  rw [←native_is_tail_input,tail_output_is_header] at run
  exact ⟨gap,trace,lower,gapBound,run,time.trans bound⟩

private theorem mid_chunk (x y : Rat) (gapM : Nat) (upperM : gapM≤2*allocationK*(fieldWidth x y)^2) :
    ∃ gapD gapG trace, 6≤gapD ∧ gapD≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤gapG ∧ gapG≤2*allocationK*(fieldWidth x y)^2 ∧
      Segment mulMachine (entryCfg (3 : Fin 17) (widen64 (actualMemory x y))
        (bankNative x y (recordM x y gapM) [] (freshGap x y) x.den y.den)) trace
        (liftCfg (6 : Fin 17) (gcdFinal x y gapM gapD gapG)) ∧
      TM0.step mulMachine (liftCfg (6 : Fin 17) (gcdFinal x y gapM gapD gapG))=
        some (entryCfg (7 : Fin 17) (widen64 (actualMemory x y))
          (bankHeader x y [recordM x y gapM,recordD x y gapD,recordG x y gapG])) ∧
      trace.length≤(2*nativeCoefficient+allocationCoefficient+feeConstant allocationK)*inputPower x y := by
  let memory := actualMemory x y
  let m := recordM x y gapM
  have hgM : ∀ r∈[m],r.gap≤2*allocationK*(fieldWidth x y)^2 := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact upperM
  have hvM : ∀ r∈[m],r.digits.length≤fieldWidth x y := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact recordM_width x y gapM
  obtain ⟨gapD,t3,lowerD,upperD,r3,l3⟩ := native_stage PSTRTMNativeMul112.nativeMulMachine 0 (by decide)
    x y m [] rfl x.den y.den (productDenominator x y) hgM hvM (five_scales x y).2.1 (productDenominator_bits x y)
    (mul_wide_runsFrom x.den y.den (freshGap x y) _ (original_native_scale_room x y))
  let d := recordD x y gapD
  have hgMD : ∀ r∈[m,d],r.gap≤2*allocationK*(fieldWidth x y)^2 := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact upperM
    · exact upperD
  have hvMD : ∀ r∈[m,d],r.digits.length≤fieldWidth x y := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact recordM_width x y gapM
    · exact recordD_width x y gapD
  obtain ⟨t4,r4,l4,_s4⟩ := actual_allocation_contract 63 2 memory [m,d] rfl (by decide) x y hgMD hvMD
  let magnitude := productMagnitude x y
  let denominator := productDenominator x y
  have hdM : m.digits=(PA17TMRatArithmeticPairEncode017.payload magnitude).head!::
      (PA17TMRatArithmeticPairEncode017.payload magnitude).tail := canonical_head_tail magnitude
  have hdD : d.digits=(PA17TMRatArithmeticPairEncode017.payload denominator).head!::
      (PA17TMRatArithmeticPairEncode017.payload denominator).tail := canonical_head_tail denominator
  obtain ⟨t5,r5,l5,_s5⟩ := cached_pair_contract 63 1 1 0 memory m [d] [] m [d] [m] d [] rfl rfl rfl rfl rfl
    (PA17TMRatArithmeticPairEncode017.payload magnitude).head! (PA17TMRatArithmeticPairEncode017.payload denominator).head!
    (PA17TMRatArithmeticPairEncode017.payload magnitude).tail (PA17TMRatArithmeticPairEncode017.payload denominator).tail
    hdM hdD (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail (freshGap x y) magnitude denominator rfl rfl
  have fee5 := (cached_fees_polynomial allocationK 1 1 0 (by decide) x y m [d] [] m [d] [m] d []
    rfl rfl rfl rfl rfl hgMD hvMD magnitude denominator rfl rfl).1
  obtain ⟨gapG,t6,lowerG,upperG,r6,l6⟩ := native_stage ROOTTMGCDDispatch018.nativeGcdMachine 1 (by decide)
    x y m [d] rfl magnitude denominator (normalizer x y) hgMD hvMD (five_scales x y).2.2.1 (normalizer_bits x y)
    (gcd_wide_runsFrom magnitude denominator (freshGap x y) _ (cached_native_scale_rooms x y).1)
  let end3 : MachineState (component (3 : Fin 17)).states :=
    ⟨carriedTailPort 63 982 0 memory,bankHeader x y [m,d]⟩
  let end4 : MachineState (component (4 : Fin 17)).states :=
    PA17TMRatArithmeticCachedOuter043.carryFinal 63 2 allocationK memory (bankWork x y m [d] (freshGap x y))
  let end5 : MachineState (component (5 : Fin 17)).states :=
    ⟨label memory (cachedPairPort 1 1 0),bankNative x y m [d] (freshGap x y) magnitude denominator⟩
  have start3 := row_entry_cfg _ (carriedTailMachine 63 PSTRTMNativeMul112.nativeMulMachine 0) memory
    (bankNative x y m [] (freshGap x y) x.den y.den)
  have start4 := row_entry_cfg _ (PA17TMRatArithmeticCachedOuter043.carryMachine 63 2 allocationK) memory (bankHeader x y [m,d])
  have start5 := row_entry_cfg _ (cachedPairMachine 63 1 1 0) memory (bankWork x y m [d] (freshGap x y))
  have start6 := row_entry_cfg _ (carriedTailMachine 63 ROOTTMGCDDispatch018.nativeGcdMachine 1) memory
    (bankNative x y m [d] (freshGap x y) magnitude denominator)
  change PSTRTMSeq005.RunsFrom (component (3 : Fin 17)).code
    (blockCfg (s:=tailCap 982 0) memory ⟨0,bankNative x y m [] (freshGap x y) x.den y.den⟩) t3 end3 at r3
  rw [←start3] at r3
  have step3 := transfer_to 3 4 (by decide) (by decide) end3 (widen64 memory) _ r3.2.2.2 (tail_decode _ 0 memory) rfl
  rw [allocated_is_work] at r4
  change PSTRTMSeq005.RunsFrom (component (4 : Fin 17)).code
    (blockCfg (s:=PA17TMRatArithmeticCachedOuter043.outerCap 2 allocationK) memory
      ⟨0,bankHeader x y [m,d]⟩) t4 end4 at r4
  rw [←start4] at r4
  have step4 := transfer_to 4 5 (by decide) (by decide) end4 (widen64 memory) _ r4.2.2.2 (allocation64_decode 2 memory _) rfl
  change PSTRTMSeq005.RunsFrom (cachedPairMachine 63 1 1 0)
    (blockCfg (s:=cachedPairCap 1 1 0) memory ⟨0,bankWork x y m [d] (freshGap x y)⟩) t5
    ⟨label memory (cachedPairPort 1 1 0),bankNative x y m [d] (freshGap x y) magnitude denominator⟩ at r5
  rw [←start5] at r5
  change PSTRTMSeq005.RunsFrom (component (5 : Fin 17)).code _ t5 end5 at r5
  have step5 := transfer_to 5 6 (by decide) (by decide) end5 (widen64 memory) _ r5.2.2.2 (cached_decode 1 1 0 memory) rfl
  change PSTRTMSeq005.RunsFrom (component (6 : Fin 17)).code
    (blockCfg (s:=tailCap 3564 1) memory ⟨0,bankNative x y m [d] (freshGap x y) magnitude denominator⟩)
    t6 (gcdFinal x y gapM gapD gapG) at r6
  rw [←start6] at r6
  have step6 := transfer_to 6 7 (by decide) (by decide) (gcdFinal x y gapM gapD gapG) (widen64 memory) _
    r6.2.2.2 (tail_decode _ 1 memory) rfl
  have sg3 := component_segment 3 _ _ _ r3
  have sg4 := component_segment 4 _ _ _ r4
  have sg5 := component_segment 5 _ _ _ r5
  have sg6 := component_segment 6 _ _ _ r6
  have sg34 := segment_append mulMachine _ _ _ _ _ _ sg3 sg4 step3
  have sg345 := segment_append mulMachine _ _ _ _ _ _ sg34 sg5 step4
  have sg3456 := segment_append mulMachine _ _ _ _ _ _ sg345 sg6 step5
  refine ⟨gapD,gapG,((liftTrace 3 t3++liftTrace 4 t4)++liftTrace 5 t5)++liftTrace 6 t6,
    lowerD,upperD,lowerG,upperG,sg3456,step6,?_⟩
  simp only [List.length_append]
  rw [liftTrace_length (3 : Fin 17) t3,liftTrace_length (4 : Fin 17) t4,
    liftTrace_length (5 : Fin 17) t5,liftTrace_length (6 : Fin 17) t6]
  have lt5 := l5.trans fee5
  change t5.length≤feeConstant allocationK*inputPower x y at lt5
  change t4.length≤allocationCoefficient*inputPower x y at l4
  calc
    _ ≤ nativeCoefficient*inputPower x y+allocationCoefficient*inputPower x y+
        feeConstant allocationK*inputPower x y+nativeCoefficient*inputPower x y :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add l3 l4) lt5) l6
    _ = _ := by ring

def prefixCoefficient : Nat := PA17TMRatArithmeticFirstRaw052.firstTimeC+2*allocationCoefficient+
  2*feeConstant allocationK+2*nativeCoefficient

theorem actual_saved_properties (x y : Rat) :
    (actualMemory x y).val%32=(PA17TMRatArithmeticBookmark014.mNx x y).val ∧
      (actualMemory x y).val/32=(if sign x then 1 else 0) ∧
      (actualMemory x y).val.testBit 5=sign x ∧ (actualMemory x y).val.testBit 2=sign y := by
  have signs := PA17TMRatArithmeticZeroCarry058.saved_sign_table (PA17TMRatArithmeticBookmark014.mNx x y) (sign x)
  exact ⟨actualMemory_retains_old x y,actualMemory_observed_sx x y,signs.1,
    signs.2.trans (PA17TMRatArithmeticBookmark014.observed_memory_bits x y).2.2.1⟩

/-- The SAME fixed controller starts on the original raw input. Three
canonical cache records are actually produced. The last global step is
not mistaken for HALT; it is the seventh real paid transition into phase7. -/
theorem mdg_segment (x y : Rat) :
    ∃ gapM gapD gapG trace last, 6≤gapM ∧ gapM≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤gapD ∧ gapD≤2*allocationK*(fieldWidth x y)^2 ∧ 6≤gapG ∧ gapG≤2*allocationK*(fieldWidth x y)^2 ∧
      Segment mulMachine (TM0.init (encode [.rational x,.rational y])) trace last ∧
      TM0.step mulMachine last=some (entryCfg (7 : Fin 17) (widen64 (actualMemory x y))
        (bankHeader x y [recordM x y gapM,recordD x y gapD,recordG x y gapG])) ∧
      trace.length≤prefixCoefficient*inputPower x y := by
  obtain ⟨gapM,firstTrace,lowerM,upperM,firstRun,firstStep,firstTime⟩ := first_chunk x y
  obtain ⟨gapD,gapG,laterTrace,lowerD,upperD,lowerG,upperG,laterRun,laterStep,laterTime⟩ := mid_chunk x y gapM upperM
  have whole := segment_append mulMachine _ _ _ _ _ _ firstRun laterRun firstStep
  refine ⟨gapM,gapD,gapG,firstTrace++laterTrace,liftCfg 6 (gcdFinal x y gapM gapD gapG),
    lowerM,upperM,lowerD,upperD,lowerG,upperG,whole,laterStep,?_⟩
  simp only [List.length_append]
  calc
    _ ≤ (PA17TMRatArithmeticFirstRaw052.firstTimeC+allocationCoefficient+feeConstant allocationK)*inputPower x y+
        (2*nativeCoefficient+allocationCoefficient+feeConstant allocationK)*inputPower x y :=
      Nat.add_le_add firstTime laterTime
    _ = _ := by unfold prefixCoefficient; ring

def prefixResourceCoefficient : Nat := 2*prefixCoefficient+2

theorem prefixCoefficient_pos : 0<prefixCoefficient := by
  unfold prefixCoefficient PA17TMRatArithmeticFirstRaw052.firstTimeC
  positivity

/-- The visited-space bound uses the returned SAME prefix trace of the
original controller, with original input length; it introduces no second
execution, intermediate input length or assumed erased workspace. -/
theorem mdg_prefix_space (x y : Rat) (trace : List (MachineState controllerCap))
    (time : trace.length≤prefixCoefficient*inputPower x y) :
    ∀ k, visitedSpace mulMachine (encode [.rational x,.rational y]).length (trace.take k)≤
      prefixResourceCoefficient*inputPower x y := by
  let i := (encode [.rational x,.rational y]).length
  have hp : i + 1 ≤ inputPower x y := by
    simpa only [inputPower,pow_one] using Nat.pow_le_pow_right
      (by omega : (1 : Nat) ≤ i + 1) (by decide : (1 : Nat)≤4)
  intro k
  have hs := PSTRTMTrace002.visitedSpace_le mulMachine i (trace.take k)
  have hk : (trace.take k).length≤trace.length := by simp only [List.length_take]; omega
  change visitedSpace mulMachine i (trace.take k)≤prefixResourceCoefficient*inputPower x y
  calc
    _ ≤ i+2*(trace.take k).length+1 := hs
    _ ≤ (i+1)+2*(prefixCoefficient*inputPower x y) := by omega
    _ ≤ inputPower x y+2*(prefixCoefficient*inputPower x y) := Nat.add_le_add_right hp _
    _ = (2*prefixCoefficient+1)*inputPower x y := by ring
    _ ≤ prefixResourceCoefficient*inputPower x y := Nat.mul_le_mul_right _ (by unfold prefixResourceCoefficient; omega)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulPrefix062
