module
public import Structure.PA17_TM_RatArithmetic_DivPrefix_067a
public import Structure.PA17_TM_RatArithmetic_RatDivFields_066a
public import Structure.PA17_TM_RatArithmetic_PairBounds_061a

/-! The actual original-codec run of the fixed division prefix. Both cross
products are stored by real native calls; bit6 is read from canonical D.
No D-zero branch or normalization tail is supplied as an assumption. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticDivPrefix067

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticPairInput050 PA17TMRatArithmeticFarLoad031
open PA17TMRatArithmeticMulController057 (widen64 row64_entry)
open PA17TMRatArithmeticFirstMul051 PA17TMRatArithmeticMulStart049
open PA17TMRatArithmeticCachedPair054 PA17TMRatArithmeticCachedOuter043
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeCache030
open PA17TMRatArithmeticRatDivFields066
open PA17TMRatArithmeticMulClosure059
open PA17TMRatArithmeticAllocationBounds056 PA17TMRatArithmeticPairBounds061
attribute [local implicit_reducible] totalStates prefixCap firstStates allocationStates pairStates recordStates observerStates
  PA17TMRatArithmeticFirstRaw052.firstCap PA17TMRatArithmeticFirstRaw052.bridgeCap
  PA17TMRatArithmeticFirstRaw052.commonCap cycleCap PA17TMRatArithmeticCachedOuter043.carryCap
  originalPairCap originalReadyCap originalFirstCap

def freshGap (x y : Rat) : Nat := allocationK*(fieldWidth x y)^2
def power (x y : Rat) : Nat := ((encode [.rational x,.rational y]).length+1)^4
def mRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (divMagnitude x y)
def dRecord (x y : Rat) (gap : Nat) : RecordSpec := resultRecord gap (divDenominator x y)
def firstTimeCoefficient : Nat := 16*allocationK+533+4096*(allocationK+2)+nativeCoefficient+(2*allocationK+53)
def prefixTimeCoefficient : Nat := firstTimeCoefficient+allocationCoefficient+feeConstant allocationK+
  nativeCoefficient+allocationCoefficient
def prefixResourceCoefficient : Nat := 2*prefixTimeCoefficient+2

theorem prefixResourceCoefficient_pos : 0<prefixResourceCoefficient := by
  unfold prefixResourceCoefficient
  omega

def firstLast (x y : Rat) (gap : Nat) : MachineState firstStates :=
  PA17TMRatArithmeticFirstRaw052.consumerState allocationK (cycleCap 63)
    (cyclePort 63 (actualMemory x y)) (bankHeader x y [mRecord x y gap])

private theorem restored (field : SourceField) (x y : Rat) :
    restoredDigits field (actualMemory x y).val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=originalDigits field x y :=
  actual_restored_with_carry field _ x y (actualMemory_retains_old x y)

private theorem first_fee_le (x y : Rat) (gap : Nat) (hg : gap≤2*allocationK*(fieldWidth x y)^2) :
    cycleFee .nx .dy (actualMemory x y).val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail (freshGap x y) gap x.num.natAbs y.den≤
        (4096*(allocationK+2)+nativeCoefficient+(2*allocationK+53))*power x y := by
  let n := (encode [.rational x,.rational y]).length+1
  let w := fieldWidth x y
  have wn : w≤n := by have h:=original_width_le_input x y;dsimp [w,n];omega
  have nn : 1≤n := Nat.succ_le_succ (Nat.zero_le _)
  have w2 : w^2≤n^4 := (Nat.pow_le_pow_left wn 2).trans (Nat.pow_le_pow_right nn (by decide))
  have w1 : w≤n^4 := wn.trans (by simpa only [pow_one] using Nat.pow_le_pow_right nn (by decide : 1≤4))
  have one : 1≤n^4 := by simpa only [one_pow] using Nat.pow_le_pow_left nn 4
  have ha : restoredDigits .nx (actualMemory x y).val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload x.num.natAbs := restored .nx x y
  have hb : restoredDigits .dy (actualMemory x y).val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload y.den := restored .dy x y
  have load0 := pairFee_uniform .nx .dy (actualMemory x y).val (numeratorDigits x).tail
    (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail (freshGap x y) x.num.natAbs y.den ha hb
  have loadWidth : pairFee .nx .dy (actualMemory x y).val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail (freshGap x y) x.num.natAbs y.den≤
      4096*((fieldWidth x y+1)*(fieldWidth x y+allocationK*(fieldWidth x y)^2+1)) := by
    simpa only [uniformBudget,original_source_width,freshGap] using load0
  have load : pairFee .nx .dy (actualMemory x y).val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail (freshGap x y) x.num.natAbs y.den≤4096*(allocationK+2)*n^4 := by
    have h := loadWidth.trans (Nat.mul_le_mul_left 4096 (allocated_uniform_polynomial allocationK x y))
    have hp := Nat.pow_le_pow_right nn (by decide : 3≤4)
    exact h.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (4096*(allocationK+2)) hp)
  have native := native_v_fee_le x.num.natAbs y.den w n (five_scales x y).1 wn nn
  have hm : natBits (x.num.natAbs*y.den)≤w := divMagnitude_bits x y
  have width := original_source_width x y
  have home : gap+2*natBits (x.num.natAbs*y.den)+2*w+49≤(2*allocationK+53)*n^4 := by
    have g := hg.trans (Nat.mul_le_mul_left (2*allocationK) w2)
    nlinarith only [g,hm,w1,one]
  change pairFee .nx .dy (actualMemory x y).val (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail (freshGap x y) x.num.natAbs y.den+
    65536*(scale x.num.natAbs y.den)^2+
    (gap+2*natBits (x.num.natAbs*y.den)+2*PA17TMRatArithmeticFarLoad031.bankWidth
      (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail+49)≤_
  rw [width]
  change _≤(4096*(allocationK+2)+nativeCoefficient+(2*allocationK+53))*n^4
  calc
    _ ≤ 4096*(allocationK+2)*n^4+nativeCoefficient*n^4+(2*allocationK+53)*n^4 :=
      Nat.add_le_add (Nat.add_le_add load native) home
    _ = _ := by ring

private theorem first_runs (x y : Rat) :
    ∃ gap trace, 6≤gap ∧ gap≤2*allocationK*(fieldWidth x y)^2 ∧
      Runs firstMachine (encode [.rational x,.rational y]) trace (firstLast x y gap) ∧
      trace.length≤firstTimeCoefficient*power x y := by
  have ha : restoredDigits .nx (actualMemory x y).val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload x.num.natAbs := restored .nx x y
  have hb : restoredDigits .dy (actualMemory x y).val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload y.den := restored .dy x y
  have hw : 1≤fieldWidth x y := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  obtain ⟨gap,tail,lower,upper,run,time,_space⟩ := cycle_contract 63 .nx .dy (actualMemory x y)
    (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail
    (denominatorDigits y).tail (freshGap x y) x.num.natAbs y.den ha hb (allocated_room _ _ _ hw (five_scales x y).1)
  have bound := new_gap_bound _ _ _ _ hw (five_scales x y).1 upper
  have input : headerTape (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail (freshGap x y)=
      (originalFinal allocationK x y).Tape := by
    change firstMInput x y [false] (freshGap x y)=_
    rw [firstMInput_allocator]
    rfl
  rw [input] at run
  change PSTRTMSeq005.RunsFrom (cycleMachine 63 .nx .dy)
    ⟨cycleEntry 63 (actualMemory x y),(originalFinal allocationK x y).Tape⟩ tail
    ⟨cyclePort 63 (actualMemory x y),bankHeader x y [mRecord x y gap]⟩ at run
  obtain ⟨trace,actual,length⟩ := PA17TMRatArithmeticFirstRaw052.combine_actual allocationK
    (cycleMachine 63 .nx .dy) (cycleEntry 63) x y _ _ run
  have fee := time.trans (first_fee_le x y gap bound)
  have inputSize := Nat.pow_le_pow_left (Nat.add_le_add_right (original_width_le_input x y) 1) 4
  refine ⟨gap,trace,lower,bound,actual,?_⟩
  calc
    _ ≤ (16*allocationK+533)*(fieldWidth x y+1)^4+tail.length := length
    _ ≤ (16*allocationK+533)*power x y+
        (4096*(allocationK+2)+nativeCoefficient+(2*allocationK+53))*power x y :=
      Nat.add_le_add (Nat.mul_le_mul_left _ inputSize) fee
    _ = firstTimeCoefficient*power x y := by unfold firstTimeCoefficient;ring

private theorem pair_fee_le (x y : Rat) (gap : Nat) (hg : gap≤2*allocationK*(fieldWidth x y)^2) :
    originalPairFee .dx .ny (actualMemory x y).val 0 (mRecord x y gap) []
      (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
      (freshGap x y) x.den y.num.natAbs≤feeConstant allocationK*power x y := by
  have hgap : ∀ r∈[mRecord x y gap],r.gap≤2*allocationK*(fieldWidth x y)^2 := by
    intro r hr;simp only [List.mem_singleton] at hr;subst r;exact hg
  have hwidth : ∀ r∈[mRecord x y gap],r.digits.length≤fieldWidth x y := by
    intro r hr;simp only [List.mem_singleton] at hr;subst r
    simpa only [mRecord,resultRecord,PSTRTMNatValue017.rawPayload,List.length_ofFn] using divMagnitude_bits x y
  obtain ⟨hone,hw,hj,hg0,hgs,hvs⟩ := produced_bank_bounds allocationK (fieldWidth x y) 0
    [mRecord x y gap] (by change 1≤5;decide) (by decide) hgap hwidth
  obtain ⟨_,hny,hdx,_⟩ := PA17TMRatArithmeticMulFields048.original_field_bits x y
  have ha : (PA17TMRatArithmeticPairEncode017.payload x.den).length≤fieldWidth x y := by
    rw [PA17TMRatArithmeticPairEncode017.payload_length];exact hdx
  have hb : (PA17TMRatArithmeticPairEncode017.payload y.num.natAbs).length≤fieldWidth x y := by
    rw [PA17TMRatArithmeticPairEncode017.payload_length];exact hny
  have ht := original_pair_time_le (chargeBase allocationK (fieldWidth x y)) 0 (freshGap x y) x.den y.num.natAbs
    hone hj hg0 .dx .ny (actualMemory x y).val (mRecord x y gap) [] (numeratorDigits x).tail
    (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    (by rw [original_source_width];exact hw) hgs hvs (ha.trans hw) (hb.trans hw)
  exact (original_pair_fee_le .dx .ny (actualMemory x y).val 0 (mRecord x y gap) []
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    (freshGap x y) x.den y.num.natAbs).trans (ht.trans (cap_original_input allocationK x y))

private theorem observe_fee (x y : Rat) (gm gd : Nat)
    (hm : gm≤2*allocationK*(fieldWidth x y)^2) (hd : gd≤2*allocationK*(fieldWidth x y)^2) :
    PA17TMRatArithmeticZeroCarry058.observeFee 0 1 (mRecord x y gm) [] []
      (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) gd (divDenominator x y)≤
        allocationCoefficient*power x y := by
  have m := divMagnitude_bits x y
  have d := divDenominator_bits x y
  have width := original_source_width x y
  change PA17TMRatArithmeticWidth018.bankWidth (false::(numeratorDigits x).tail)
    (false::(denominatorDigits x).tail) (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)=fieldWidth x y at width
  have hg : totalGap (mRecord x y gm::PA17TMRatArithmeticZeroCarry058.observedRecords [] [] gd (divDenominator x y))≤
      10*allocationK*(fieldWidth x y)^2 := by
    simp only [PA17TMRatArithmeticZeroCarry058.observedRecords,List.nil_append,totalGap,mRecord,resultRecord,Nat.add_zero]
    nlinarith only [hm,hd]
  have hv : totalWidth (mRecord x y gm::PA17TMRatArithmeticZeroCarry058.observedRecords [] [] gd (divDenominator x y))≤
      5*fieldWidth x y := by
    simp only [PA17TMRatArithmeticZeroCarry058.observedRecords,List.nil_append,totalWidth,mRecord,resultRecord,
      PSTRTMNatValue017.rawPayload,List.length_ofFn,Nat.add_zero]
    omega
  have high := observe_fee_le (mRecord x y gm) [] [] (false::(numeratorDigits x).tail)
    (false::(denominatorDigits x).tail) (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
    gd (divDenominator x y) (fieldWidth x y) ((encode [.rational x,.rational y]).length+1)
    hg hv (by simp only [totalGap];omega) (by simp only [totalWidth];omega) d (by rw [width])
    (by have h:=original_width_le_input x y;omega) (Nat.succ_le_succ (Nat.zero_le _))
  apply le_trans _ high
  unfold PA17TMRatArithmeticZeroCarry058.observeFee PA17TMRatArithmeticZeroCarry058.readFee PA17TMRatArithmeticZeroCarry058.returnFee
  omega

private theorem row_entry (states : Nat) (code : Machine (totalStates 63 states)) (memory : Fin 64) (tape : Tape Bool) :
    (⟨(PA17TMRatArithmeticMulController057.row64Component states code).entry (widen64 memory),tape⟩ :
      MachineState (totalStates 63 states))=blockCfg memory (⟨0,tape⟩ : MachineState states) := by
  rw [row64_entry]
  rfl

private theorem transfer_to (phase next : Fin 5) (hp : phase.val<4) (hn : nextPhase phase=next)
    (last : MachineState (component phase).states) (memory : Fin 128) (tape : Tape Bool)
    (halt : TM0.step (component phase).code last=none)
    (decode : (component phase).decode last.q=memory) (whole : last.Tape=tape) :
    TM0.step prefixMachine (liftCfg phase last)=some (entryCfg next memory tape) := by
  rw [paid_transfer phase hp last halt,hn,decode,whole]

private theorem retarget_first {states : Nat} (code : Machine states)
    (first next last : MachineState states) (trace : List (MachineState states))
    (same : first=next) (run : Segment code first trace last) : Segment code next trace last :=
  same ▸ run

theorem original_prefix_runs (x y : Rat) :
    ∃ gm gd trace, 6≤gm ∧ gm≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤gd ∧ gd≤2*allocationK*(fieldWidth x y)^2 ∧
      Runs prefixMachine (encode [.rational x,.rational y]) trace (prefixFinal x y gm gd) ∧
      trace.length≤prefixTimeCoefficient*power x y := by
  let memory := actualMemory x y
  obtain ⟨gm,t0,lm,um,r0,len0⟩ := first_runs x y
  let m := mRecord x y gm
  have hgap : ∀ r∈[m],r.gap≤2*allocationK*(fieldWidth x y)^2 := by
    intro r hr;simp only [List.mem_singleton] at hr;subst r;exact um
  have hwidth : ∀ r∈[m],r.digits.length≤fieldWidth x y := by
    intro r hr;simp only [List.mem_singleton] at hr;subst r
    simpa only [m,mRecord,resultRecord,PSTRTMNatValue017.rawPayload,List.length_ofFn] using divMagnitude_bits x y
  obtain ⟨t1,r1,len1,_space1⟩ := actual_allocation_contract 63 1 memory [m] rfl (by decide) x y hgap hwidth
  have ha : restoredDigits .dx memory.val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload x.den := restored .dx x y
  have hb : restoredDigits .ny memory.val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload y.num.natAbs := restored .ny x y
  obtain ⟨t2,r2,len2,_space2⟩ := original_pair_contract 63 .dx .ny 0 memory m [] rfl (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    (freshGap x y) x.den y.num.natAbs ha hb
  let archive := true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m []
  have hw : 1≤fieldWidth x y := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  obtain ⟨gd,td,lastD,rd,wholeD,ld,ud,lenD,_spaceD⟩ := mul_allocated_runsFrom x.den y.num.natAbs (fieldWidth x y)
    archive hw (five_scales x y).2.1
  have ug := new_gap_bound _ _ _ _ hw (five_scales x y).2.1 ud
  let observedInput := PA17TMRatArithmeticReturnHome037.homeInput (sign x) [false]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [dRecord x y gd] []
  have whole : lastD.Tape=observedInput := wholeD.trans
    (newRecord_home (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [] gd (divDenominator x y))
  have last_eq : lastD=(⟨lastD.q,observedInput⟩ : MachineState 1016) := by
    cases lastD
    simp_all only
  rw [last_eq] at rd
  change PSTRTMSeq005.RunsFrom mulCacheMachine
    (⟨0,tailInput (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [] (freshGap x y) x.den y.num.natAbs⟩ : MachineState 1016)
    td ⟨lastD.q,observedInput⟩ at rd
  rw [←native_is_tail_input x y m [] (freshGap x y) x.den y.num.natAbs] at rd
  have r3 := record_runs memory _ _ td rd
  let t3 := td.map (blockCfg (s:=1016) memory)
  obtain ⟨t4,r4,len4,_space4⟩ := PA17TMRatArithmeticZeroCarry058.observe_contract 0 1 memory m [] [] gd
    (divDenominator x y) rfl rfl (sign x) [false] (false::(numeratorDigits x).tail)
    (false::(denominatorDigits x).tail) (false::(numeratorDigits y).tail) (denominatorDigits y).tail
  have start1 : (⟨(component (1 : Fin 5)).entry (widen64 memory),bankHeader x y [m]⟩ : MachineState (component (1 : Fin 5)).states)=
      carryEntry 63 1 allocationK memory (bankHeader x y [m]) := row_entry _ (carryMachine 63 1 allocationK) memory _
  have start2 : (⟨(component (2 : Fin 5)).entry (widen64 memory),bankWork x y m [] (freshGap x y)⟩ : MachineState (component (2 : Fin 5)).states)=
      blockCfg memory (⟨0,bankWork x y m [] (freshGap x y)⟩ : MachineState (originalPairCap 0)) :=
    row_entry _ (originalPairMachine 63 .dx .ny 0) memory _
  have start3 : (⟨(component (3 : Fin 5)).entry (widen64 memory),bankNative x y m [] (freshGap x y) x.den y.num.natAbs⟩ :
      MachineState (component (3 : Fin 5)).states)=blockCfg memory
      (⟨0,bankNative x y m [] (freshGap x y) x.den y.num.natAbs⟩ : MachineState 1016) := row_entry 1016 recordMachine memory _
  let observerStart : MachineState observerStates :=
    ⟨PA17TMRatArithmeticZeroCarry058.observeEntry 0 1
      (PA17TMRatArithmeticMulController057.narrow64 (widen64 memory)),observedInput⟩
  let end0 : MachineState (component (0 : Fin 5)).states := firstLast x y gm
  let end1 : MachineState (component (1 : Fin 5)).states := carryFinal 63 1 allocationK memory (bankWork x y m [] (freshGap x y))
  let end2 : MachineState (component (2 : Fin 5)).states := blockCfg memory
    (⟨originalPairPort 0,bankNative x y m [] (freshGap x y) x.den y.num.natAbs⟩ : MachineState (originalPairCap 0))
  let end3 : MachineState (component (3 : Fin 5)).states := blockCfg memory (⟨lastD.q,observedInput⟩ : MachineState 1016)
  let end4 : MachineState (component (4 : Fin 5)).states :=
    ⟨PA17TMRatArithmeticZeroCarry058.observePort 0 1 (observed x y),postTape x y gm gd⟩
  have r0From : PSTRTMSeq005.RunsFrom firstMachine (TM0.init (encode [.rational x,.rational y])) t0 end0 :=
    ⟨r0.1,r0.2.1,r0.2.2.1,r0.2.2.2.1⟩
  change PSTRTMSeq005.RunsFrom (component (0 : Fin 5)).code _ t0 end0 at r0From
  have decode0 : (component (0 : Fin 5)).decode end0.q=widen64 memory :=
    PA17TMRatArithmeticMulController057.first_decode memory (bankHeader x y [m])
  have step0 := transfer_to 0 1 (by decide) (by decide) end0 (widen64 memory) _ r0From.2.2.2 decode0 rfl
  rw [allocated_is_work] at r1
  change PSTRTMSeq005.RunsFrom (component (1 : Fin 5)).code (carryEntry 63 1 allocationK memory (bankHeader x y [m])) t1 end1 at r1
  rw [←start1] at r1
  have decode1 : (component (1 : Fin 5)).decode end1.q=widen64 memory :=
    PA17TMRatArithmeticMulController057.row64_decode (outerCap 1 allocationK)
      (carryMachine 63 1 allocationK) memory (outerPort 1 allocationK)
  have step1 := transfer_to 1 2 (by decide) (by decide) end1 (widen64 memory) _ r1.2.2.2 decode1 rfl
  change PSTRTMSeq005.RunsFrom (component (2 : Fin 5)).code
    (blockCfg memory (⟨0,bankWork x y m [] (freshGap x y)⟩ : MachineState (originalPairCap 0))) t2 end2 at r2
  rw [←start2] at r2
  have decode2 : (component (2 : Fin 5)).decode end2.q=widen64 memory :=
    PA17TMRatArithmeticMulController057.row64_decode _ (originalPairMachine 63 .dx .ny 0) memory (originalPairPort 0)
  have step2 := transfer_to 2 3 (by decide) (by decide) end2 (widen64 memory) _ r2.2.2.2 decode2 rfl
  rw [←start3] at r3
  change PSTRTMSeq005.RunsFrom (component (3 : Fin 5)).code _ t3 end3 at r3
  have decode3 : (component (3 : Fin 5)).decode end3.q=widen64 memory := record_decode memory lastD.q
  have step3 := transfer_to 3 4 (by decide) (by decide) end3 (widen64 memory) _ r3.2.2.2 decode3 rfl
  change PSTRTMSeq005.RunsFrom (PA17TMRatArithmeticZeroCarry058.observeMachine 0 1)
    (⟨PA17TMRatArithmeticZeroCarry058.observeEntry 0 1 memory,observedInput⟩ : MachineState observerStates)
    t4 (⟨PA17TMRatArithmeticZeroCarry058.observePort 0 1 (observed x y),postTape x y gm gd⟩ : MachineState observerStates) at r4
  have r4Entry : PSTRTMSeq005.RunsFrom (PA17TMRatArithmeticZeroCarry058.observeMachine 0 1)
      observerStart t4 (⟨PA17TMRatArithmeticZeroCarry058.observePort 0 1 (observed x y),postTape x y gm gd⟩ : MachineState observerStates) := by
    dsimp only [observerStart]
    rw [PA17TMRatArithmeticMulController057.narrow_widen]
    exact r4
  change PSTRTMSeq005.RunsFrom (component (4 : Fin 5)).code observerStart t4 end4 at r4Entry
  have s0 := component_segment 0 _ _ _ r0From
  have s0Init := retarget_first (states:=prefixCap) prefixMachine _ _ _ _
    (initial_mapped (encode [.rational x,.rational y])) s0
  have s1 := component_segment 1 _ _ _ r1
  have s2 := component_segment 2 _ _ _ r2
  have s3 := component_segment 3 _ _ _ r3
  have s4 := component_segment 4 _ _ _ r4Entry
  have joined01 := segment_append prefixMachine _ _ _ _ _ _ s0Init s1 step0
  have joined012 := segment_append prefixMachine _ _ _ _ _ _ joined01 s2 step1
  have joined0123 := segment_append prefixMachine _ _ _ _ _ _ joined012 s3 step2
  have joined := segment_append prefixMachine _ _ _ _ _ _ joined0123 s4 step3
  have halted := final_halt end4 r4Entry.2.2.2
  have last4 : liftCfg (4 : Fin 5) end4=prefixFinal x y gm gd := rfl
  rw [last4] at joined halted
  let trace := (((liftTrace 0 t0++liftTrace 1 t1)++liftTrace 2 t2)++liftTrace 3 t3)++liftTrace 4 t4
  have actual : Runs prefixMachine (encode [.rational x,.rational y]) trace (prefixFinal x y gm gd) :=
    PSTRTMTrace002.runs_of_chain _ _ _ _ joined.1 joined.2.1 joined.2.2 halted
  have fee2 := len2.trans (pair_fee_le x y gm um)
  have wn : fieldWidth x y≤(encode [.rational x,.rational y]).length+1 := by have h:=original_width_le_input x y;omega
  have fee3 := lenD.trans (native_v_fee_le x.den y.num.natAbs _ _ (five_scales x y).2.1 wn (Nat.succ_le_succ (Nat.zero_le _)))
  have fee4 := len4.trans (observe_fee x y gm gd um ug)
  refine ⟨gm,gd,trace,lm,um,ld,ug,actual,?_⟩
  simp only [trace,List.length_append]
  rw [liftTrace_length (0 : Fin 5) t0,liftTrace_length (1 : Fin 5) t1,liftTrace_length (2 : Fin 5) t2,
    liftTrace_length (3 : Fin 5) t3,liftTrace_length (4 : Fin 5) t4]
  have t3length : t3.length=td.length := List.length_map _
  change t1.length≤allocationCoefficient*power x y at len1
  change td.length≤nativeCoefficient*power x y at fee3
  have fee3Lift : t3.length≤nativeCoefficient*power x y := t3length.trans_le fee3
  calc
    _ ≤ (((firstTimeCoefficient*power x y+allocationCoefficient*power x y)+feeConstant allocationK*power x y)+
        nativeCoefficient*power x y)+allocationCoefficient*power x y :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add len0 len1) fee2) fee3Lift) fee4
    _ = prefixTimeCoefficient*power x y := by unfold prefixTimeCoefficient;ring

theorem original_prefix_contract (x y : Rat) :
    ∃ gm gd trace, 6≤gm ∧ gm≤2*allocationK*(fieldWidth x y)^2 ∧
      6≤gd ∧ gd≤2*allocationK*(fieldWidth x y)^2 ∧
      Runs prefixMachine (encode [.rational x,.rational y]) trace (prefixFinal x y gm gd) ∧
      trace.length≤prefixResourceCoefficient*power x y ∧
      ∀ n, visitedSpace prefixMachine (encode [.rational x,.rational y]).length (trace.take n)≤
        prefixResourceCoefficient*power x y := by
  obtain ⟨gm,gd,trace,lm,um,ld,ud,run,time⟩ := original_prefix_runs x y
  let i := (encode [.rational x,.rational y]).length
  have hi : i+1≤(i+1)^4 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le i)) (by decide : 1≤4))
  have hc : prefixTimeCoefficient≤prefixResourceCoefficient := by unfold prefixResourceCoefficient;omega
  refine ⟨gm,gd,trace,lm,um,ld,ud,run,time.trans (Nat.mul_le_mul_right _ hc),?_⟩
  intro n
  have cells := PSTRTMTrace002.visitedSpace_le prefixMachine i (trace.take n)
  have taken : (trace.take n).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  change trace.length≤prefixTimeCoefficient*(i+1)^4 at time
  change visitedSpace prefixMachine i (trace.take n)≤prefixResourceCoefficient*(i+1)^4
  calc
    _ ≤ i+2*(trace.take n).length+1 := cells
    _ ≤ i+2*(prefixTimeCoefficient*(i+1)^4)+1 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (taken.trans time)) i) 1
    _ = (i+1)+2*(prefixTimeCoefficient*(i+1)^4) := by ac_rfl
    _ ≤ (i+1)^4+2*(prefixTimeCoefficient*(i+1)^4) := Nat.add_le_add_right hi _
    _ = (2*prefixTimeCoefficient+1)*(i+1)^4 := by ring
    _ ≤ prefixResourceCoefficient*(i+1)^4 := Nat.mul_le_mul_right _ (by unfold prefixResourceCoefficient;omega)

theorem observed_yzero (x y : Rat) : (observed x y).val/64=if decide (y=0) then 1 else 0 := by
  have flag : decide (x.den*y.num.natAbs=0)=decide (y=0) :=
    observed_denominator_zero x y _ _ rfl rfl
  change (PA17TMRatArithmeticZeroCarry058.observedMemory (actualMemory x y) _).val/64=_
  rw [PA17TMRatArithmeticZeroCarry058.observedMemory_zero_bit,flag]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticDivPrefix067
