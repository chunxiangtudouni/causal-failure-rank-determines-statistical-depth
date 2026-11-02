module
public import Structure.PA17_TM_RatArithmetic_AddSubController_075b
public import Structure.PA17_TM_RatArithmetic_AddSubBounds_073a
public import Structure.PA17_TM_RatArithmetic_AddSubPrefix_074b

/-! Actual G and U rounds of the same fixed addition/subtraction
controller. Each round allocates, copies two real resident records,
executes a native call, physically returns home and pays its next port. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubNormalize077

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticSignedSumFields072 PA17TMRatArithmeticAddSubController075
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticCachedOuter043 PA17TMRatArithmeticCachedPair054
open PA17TMRatArithmeticMulClosure059 (bankHeader bankNative bankWork allocated_is_work native_is_tail_input tail_output_is_header)
open PA17TMRatArithmeticMulController057 (widen64 row64_decode)
open PA17TMRatArithmeticAddSubPrefix074 (RecordBound BankBound result_bound bank_nil bank_cons row_entry retarget_run_first)
attribute [local implicit_reducible] totalStates controllerCap
  PA17TMRatArithmeticCachedOuter043.carryCap carriedTailCap tailCap nativeRecordCap cachedPairCap

def roundCoefficient : Nat := PA17TMRatArithmeticAddSubBounds073.resourceCoefficient+
  2*PA17TMRatArithmeticAddSubBounds073.timeCoefficient

theorem roundCoefficient_pos : 0<roundCoefficient := by
  have h := PA17TMRatArithmeticAddSubBounds073.coefficients_pos.1
  unfold roundCoefficient
  omega

private theorem allocation_round (total : Nat) (ht : total≤9) (memory : Fin 64) (x y : Rat)
    (first : RecordSpec) (later : List RecordSpec) (hc : (first::later).length=total)
    (bound : BankBound x y (first::later)) :
    ∃ trace,PSTRTMSeq005.RunsFrom (carryMachine 63 total allocationK)
      (carryEntry 63 total allocationK memory (bankHeader x y (first::later))) trace
      (carryFinal 63 total allocationK memory (bankWork x y first later (allocationK*(fieldWidth x y)^2))) ∧
      trace.length≤PA17TMRatArithmeticAddSubBounds073.resourceCoefficient*originalPower x y := by
  obtain ⟨trace,run,time,_space⟩ := PA17TMRatArithmeticAddSubBounds073.actual_allocation_contract9
    63 total memory ht (first::later) hc x y (fun r hr => (bound r hr).1) (fun r hr => (bound r hr).2)
  rw [allocated_is_work] at run
  exact ⟨trace,run,time⟩

private theorem cached_round (j aLater bLater : Nat) (hj : j≤8) (memory : Fin 64) (x y : Rat) (first : RecordSpec)
    (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hc : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (hA : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hB : followingB.length=bLater)
    (bound : BankBound x y (first::records)) (a b : Nat)
    (ha : sourceA.digits=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : sourceB.digits=PA17TMRatArithmeticPairEncode017.payload b) :
    ∃ trace,PSTRTMSeq005.RunsFrom (cachedPairMachine 63 j aLater bLater)
      (blockCfg memory (⟨0,bankWork x y first records (allocationK*(fieldWidth x y)^2)⟩ : MachineState (cachedPairCap j aLater bLater))) trace
      (blockCfg memory (⟨cachedPairPort j aLater bLater,bankNative x y first records (allocationK*(fieldWidth x y)^2) a b⟩ :
        MachineState (cachedPairCap j aLater bLater))) ∧
      trace.length≤PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y := by
  obtain ⟨trace,run,time,_space⟩ := cached_pair_contract 63 j aLater bLater memory first records beforeA sourceA
    followingA beforeB sourceB followingB hc hbankA hA hbankB hB
    (PA17TMRatArithmeticPairEncode017.payload a).head! (PA17TMRatArithmeticPairEncode017.payload b).head!
    (PA17TMRatArithmeticPairEncode017.payload a).tail (PA17TMRatArithmeticPairEncode017.payload b).tail
    (ha.trans (canonical_head_tail a)) (hb.trans (canonical_head_tail b)) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    (allocationK*(fieldWidth x y)^2) a b ha hb
  have source := PA17TMRatArithmeticPairInput050.original_source_width x y
  have fee := (PA17TMRatArithmeticAddSubBounds073.cached_fees9 j aLater bLater hj x y first records beforeA sourceA
    followingA beforeB sourceB followingB hc hbankA hA hbankB hB (fun r hr => (bound r hr).1)
    (fun r hr => (bound r hr).2) (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail (by rw [source]) a b ha hb).1
  exact ⟨trace,run,time.trans fee⟩

private theorem native_round {states : Nat} (native : Machine states) (j : Nat) (hj : j≤8)
    (memory : Fin 64) (x y : Rat) (first : RecordSpec) (later : List RecordSpec) (hc : later.length=j)
    (bound : BankBound x y (first::later)) (a b value : Nat)
    (hs : PA17TMRatArithmeticNativeCache030.scale a b≤4*fieldWidth x y) (hv : natBits value≤fieldWidth x y)
    (actual : WideCacheResult native a b value
      (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
        (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) first later) (allocationK*(fieldWidth x y)^2)) :
    ∃ gap trace,6≤gap ∧ gap≤2*allocationK*(fieldWidth x y)^2 ∧
      PSTRTMSeq005.RunsFrom (carriedTailMachine 63 native j)
        (⟨carriedTailEntry 63 states j memory,bankNative x y first later (allocationK*(fieldWidth x y)^2) a b⟩ :
          MachineState (carriedTailCap 63 states j)) trace
        (⟨carriedTailPort 63 states j memory,bankHeader x y (first::(later++[resultRecord gap value]))⟩ :
          MachineState (carriedTailCap 63 states j)) ∧
      trace.length≤PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y := by
  obtain ⟨gap,trace,lower,upper,run,time,_space⟩ := carriedTail_contract 63 native j memory first later hc
    (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail (allocationK*(fieldWidth x y)^2) a b value actual
  have hw : 1≤fieldWidth x y := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  have ug := new_gap_bound a b (fieldWidth x y) gap hw hs upper
  rw [←native_is_tail_input x y first later (allocationK*(fieldWidth x y)^2) a b,tail_output_is_header] at run
  have hlen : (first::later).length≤9 := by simp only [List.length_cons,hc];omega
  obtain ⟨hg,hwB⟩ := PA17TMRatArithmeticAddSubBounds073.cache_totals9 x y (first::later) hlen
    (fun r hr => (bound r hr).1) (fun r hr => (bound r hr).2)
  have source := PA17TMRatArithmeticPairInput050.original_source_width x y
  change PA17TMRatArithmeticWidth018.bankWidth (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)=fieldWidth x y at source
  have fee := PA17TMRatArithmeticAddSubBounds073.native_tail_fee9 j hj x y first later
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) gap a b value hg hwB ug hs hv (by rw [source])
  exact ⟨gap,trace,lower,ug,run,time.trans fee⟩

theorem g_segment (subtract : Bool) (x y : Rat) (gm gn ge gp gq gr : Nat)
    (hM : gm≤2*allocationK*(fieldWidth x y)^2) (hN : gn≤2*allocationK*(fieldWidth x y)^2)
    (hE : ge≤2*allocationK*(fieldWidth x y)^2) (hP : gp≤2*allocationK*(fieldWidth x y)^2)
    (hQ : gq≤2*allocationK*(fieldWidth x y)^2) (hR : gr≤2*allocationK*(fieldWidth x y)^2) :
    ∃ gg trace last,6≤gg ∧ gg≤2*allocationK*(fieldWidth x y)^2 ∧
      Segment (addSubMachine subtract) (entryCfg (6 : Fin 19) (widen64 (resultMemory subtract x y))
        (bankHeader x y [mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq,rRecord subtract x y gr])) trace last ∧
      TM0.step (addSubMachine subtract) last=some (entryCfg (9 : Fin 19) (widen64 (resultMemory subtract x y))
        (bankHeader x y [mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq,rRecord subtract x y gr,gRecord subtract x y gg])) ∧
      trace.length≤roundCoefficient*originalPower x y := by
  let memory := resultMemory subtract x y
  let m := mRecord x y gm;let n := nRecord x y gn;let e := eRecord x y ge
  let p := pRecord x y gp;let q := qRecord x y gq;let r := rRecord subtract x y gr
  let gap := allocationK*(fieldWidth x y)^2
  have bm : RecordBound x y m := result_bound x y gm _ hM (left_bits x y)
  have bn : RecordBound x y n := result_bound x y gn _ hN (right_bits x y)
  have be : RecordBound x y e := result_bound x y ge _ hE (denominator_bits x y)
  have bp : RecordBound x y p := result_bound x y gp _ hP (difference_bits x y).1
  have bq : RecordBound x y q := result_bound x y gq _ hQ (difference_bits x y).2
  have br : RecordBound x y r := result_bound x y gr _ hR (sum_bits subtract x y)
  have bound : BankBound x y [m,n,e,p,q,r] := bank_cons x y m _ bm (bank_cons x y n _ bn
    (bank_cons x y e _ be (bank_cons x y p _ bp (bank_cons x y q _ bq (bank_cons x y r [] br (bank_nil x y))))))
  obtain ⟨ta,ra,la⟩ := allocation_round 6 (by decide) memory x y m [n,e,p,q,r] rfl bound
  obtain ⟨tb,rb,lb⟩ := cached_round 5 0 3 (by decide) memory x y m [n,e,p,q,r]
    [m,n,e,p,q] r [] [m,n] e [p,q,r] rfl rfl rfl rfl rfl bound
    (sumMagnitude subtract x y) (commonDenominator x y) rfl rfl
  obtain ⟨_,_,_,_,_,_,size,_,_⟩ := nine_scales subtract x y
  have hw : 1≤fieldWidth x y := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  have actual := gcd_allocated_runsFrom (sumMagnitude subtract x y) (commonDenominator x y) (fieldWidth x y)
    (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [n,e,p,q,r]) hw size
  obtain ⟨gg,tc,lower,upper,rc,lc⟩ := native_round ROOTTMGCDDispatch018.nativeGcdMachine 5 (by decide)
    memory x y m [n,e,p,q,r] rfl bound (sumMagnitude subtract x y) (commonDenominator x y)
    (normalizer subtract x y) size (normalizer_bits subtract x y) actual
  let g := gRecord subtract x y gg
  let endA : MachineState (PA17TMRatArithmeticCachedOuter043.carryCap 63 6 allocationK) :=
    carryFinal 63 6 allocationK memory (bankWork x y m [n,e,p,q,r] gap)
  let endB : MachineState (totalStates 63 (cachedPairCap 5 0 3)) := blockCfg memory
    (⟨cachedPairPort 5 0 3,bankNative x y m [n,e,p,q,r] gap (sumMagnitude subtract x y) (commonDenominator x y)⟩ :
      MachineState (cachedPairCap 5 0 3))
  let endC : MachineState (carriedTailCap 63 3564 5) :=
    ⟨carriedTailPort 63 3564 5 memory,bankHeader x y [m,n,e,p,q,r,g]⟩
  have startA := row_entry (outerCap 6 allocationK) (carryMachine 63 6 allocationK) memory (bankHeader x y [m,n,e,p,q,r])
  have startB := row_entry (cachedPairCap 5 0 3) (cachedPairMachine 63 5 0 3) memory (bankWork x y m [n,e,p,q,r] gap)
  have startC := row_entry (tailCap 3564 5) (carriedTailMachine 63 ROOTTMGCDDispatch018.nativeGcdMachine 5) memory
    (bankNative x y m [n,e,p,q,r] gap (sumMagnitude subtract x y) (commonDenominator x y))
  have runA := retarget_run_first (states:=PA17TMRatArithmeticCachedOuter043.carryCap 63 6 allocationK)
    (carryMachine 63 6 allocationK) _ _ _ _ startA.symm ra
  have runB := retarget_run_first (states:=totalStates 63 (cachedPairCap 5 0 3))
    (cachedPairMachine 63 5 0 3) _ _ _ _ startB.symm rb
  have runC := retarget_run_first (states:=carriedTailCap 63 3564 5)
    (carriedTailMachine 63 ROOTTMGCDDispatch018.nativeGcdMachine 5) _ _ _ _ startC.symm rc
  change PSTRTMSeq005.RunsFrom (component (6 : Fin 19)).code _ ta endA at runA
  change PSTRTMSeq005.RunsFrom (component (7 : Fin 19)).code _ tb endB at runB
  change PSTRTMSeq005.RunsFrom (component (8 : Fin 19)).code _ tc endC at runC
  have dA : (component (6 : Fin 19)).decode endA.q=widen64 memory :=
    row64_decode (outerCap 6 allocationK) (carryMachine 63 6 allocationK) memory (outerPort 6 allocationK)
  have dB : (component (7 : Fin 19)).decode endB.q=widen64 memory :=
    row64_decode (cachedPairCap 5 0 3) (cachedPairMachine 63 5 0 3) memory (cachedPairPort 5 0 3)
  have dC : (component (8 : Fin 19)).decode endC.q=widen64 memory :=
    row64_decode (tailCap 3564 5) (carriedTailMachine 63 ROOTTMGCDDispatch018.nativeGcdMachine 5) memory (tailPort 3564 5)
  have stepA := transfer_to subtract 6 7 (by decide) endA (widen64 memory) (widen64 memory) _ runA.2.2.2 dA rfl rfl rfl
  have stepB := transfer_to subtract 7 8 (by decide) endB (widen64 memory) (widen64 memory) _ runB.2.2.2 dB rfl rfl rfl
  have stepC := transfer_to subtract 8 9 (by decide) endC (widen64 memory) (widen64 memory) _ runC.2.2.2 dC rfl rfl rfl
  have sA := component_segment subtract 6 _ _ _ runA
  have sB := component_segment subtract 7 _ _ _ runB
  have sC := component_segment subtract 8 _ _ _ runC
  have ab := segment_append (addSubMachine subtract) _ _ _ _ _ _ sA sB stepA
  have joined := segment_append (addSubMachine subtract) _ _ _ _ _ _ ab sC stepB
  let trace := (liftTrace (6 : Fin 19) ta++liftTrace (7 : Fin 19) tb)++liftTrace (8 : Fin 19) tc
  refine ⟨gg,trace,liftCfg (8 : Fin 19) endC,lower,upper,joined,stepC,?_⟩
  simp only [trace,List.length_append]
  rw [liftTrace_length (6 : Fin 19) ta,liftTrace_length (7 : Fin 19) tb,liftTrace_length (8 : Fin 19) tc]
  calc
    _ ≤ PA17TMRatArithmeticAddSubBounds073.resourceCoefficient*originalPower x y+
        PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y+
        PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y := Nat.add_le_add (Nat.add_le_add la lb) lc
    _ = _ := by unfold roundCoefficient;ring

theorem u_segment (subtract : Bool) (x y : Rat) (gm gn ge gp gq gr gg : Nat)
    (hM : gm≤2*allocationK*(fieldWidth x y)^2) (hN : gn≤2*allocationK*(fieldWidth x y)^2)
    (hE : ge≤2*allocationK*(fieldWidth x y)^2) (hP : gp≤2*allocationK*(fieldWidth x y)^2)
    (hQ : gq≤2*allocationK*(fieldWidth x y)^2) (hR : gr≤2*allocationK*(fieldWidth x y)^2)
    (hG : gg≤2*allocationK*(fieldWidth x y)^2) :
    ∃ gu trace last,6≤gu ∧ gu≤2*allocationK*(fieldWidth x y)^2 ∧
      Segment (addSubMachine subtract) (entryCfg (9 : Fin 19) (widen64 (resultMemory subtract x y))
        (bankHeader x y [mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq,rRecord subtract x y gr,gRecord subtract x y gg])) trace last ∧
      TM0.step (addSubMachine subtract) last=some (entryCfg (12 : Fin 19) (widen64 (resultMemory subtract x y))
        (bankHeader x y [mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq,rRecord subtract x y gr,gRecord subtract x y gg,uRecord subtract x y gu])) ∧
      trace.length≤roundCoefficient*originalPower x y := by
  let memory := resultMemory subtract x y
  let m := mRecord x y gm;let n := nRecord x y gn;let e := eRecord x y ge
  let p := pRecord x y gp;let q := qRecord x y gq;let r := rRecord subtract x y gr;let g := gRecord subtract x y gg
  let gap := allocationK*(fieldWidth x y)^2
  have bm : RecordBound x y m := result_bound x y gm _ hM (left_bits x y)
  have bn : RecordBound x y n := result_bound x y gn _ hN (right_bits x y)
  have be : RecordBound x y e := result_bound x y ge _ hE (denominator_bits x y)
  have bp : RecordBound x y p := result_bound x y gp _ hP (difference_bits x y).1
  have bq : RecordBound x y q := result_bound x y gq _ hQ (difference_bits x y).2
  have br : RecordBound x y r := result_bound x y gr _ hR (sum_bits subtract x y)
  have bg : RecordBound x y g := result_bound x y gg _ hG (normalizer_bits subtract x y)
  have bound : BankBound x y [m,n,e,p,q,r,g] := bank_cons x y m _ bm (bank_cons x y n _ bn
    (bank_cons x y e _ be (bank_cons x y p _ bp (bank_cons x y q _ bq (bank_cons x y r _ br
      (bank_cons x y g [] bg (bank_nil x y)))))))
  obtain ⟨ta,ra,la⟩ := allocation_round 7 (by decide) memory x y m [n,e,p,q,r,g] rfl bound
  obtain ⟨tb,rb,lb⟩ := cached_round 6 1 0 (by decide) memory x y m [n,e,p,q,r,g]
    [m,n,e,p,q] r [g] [m,n,e,p,q,r] g [] rfl rfl rfl rfl rfl bound
    (sumMagnitude subtract x y) (normalizer subtract x y) rfl rfl
  obtain ⟨_,_,_,_,_,_,_,size,_⟩ := nine_scales subtract x y
  have hw : 1≤fieldWidth x y := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  have actual := quotient_allocated_runsFrom (sumMagnitude subtract x y) (normalizer subtract x y) (fieldWidth x y)
    (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [n,e,p,q,r,g]) hw size
  obtain ⟨gu,tc,lower,upper,rc,lc⟩ := native_round PA17TMDivisionFull012.quotientMachine 6 (by decide)
    memory x y m [n,e,p,q,r,g] rfl bound (sumMagnitude subtract x y) (normalizer subtract x y)
    (quotientNumerator subtract x y) size (quotient_bits subtract x y).1 actual
  let u := uRecord subtract x y gu
  let endA : MachineState (PA17TMRatArithmeticCachedOuter043.carryCap 63 7 allocationK) :=
    carryFinal 63 7 allocationK memory (bankWork x y m [n,e,p,q,r,g] gap)
  let endB : MachineState (totalStates 63 (cachedPairCap 6 1 0)) := blockCfg memory
    (⟨cachedPairPort 6 1 0,bankNative x y m [n,e,p,q,r,g] gap (sumMagnitude subtract x y) (normalizer subtract x y)⟩ :
      MachineState (cachedPairCap 6 1 0))
  let endC : MachineState (carriedTailCap 63 1136 6) :=
    ⟨carriedTailPort 63 1136 6 memory,bankHeader x y [m,n,e,p,q,r,g,u]⟩
  have startA := row_entry (outerCap 7 allocationK) (carryMachine 63 7 allocationK) memory (bankHeader x y [m,n,e,p,q,r,g])
  have startB := row_entry (cachedPairCap 6 1 0) (cachedPairMachine 63 6 1 0) memory (bankWork x y m [n,e,p,q,r,g] gap)
  have startC := row_entry (tailCap 1136 6) (carriedTailMachine 63 PA17TMDivisionFull012.quotientMachine 6) memory
    (bankNative x y m [n,e,p,q,r,g] gap (sumMagnitude subtract x y) (normalizer subtract x y))
  have runA := retarget_run_first (states:=PA17TMRatArithmeticCachedOuter043.carryCap 63 7 allocationK)
    (carryMachine 63 7 allocationK) _ _ _ _ startA.symm ra
  have runB := retarget_run_first (states:=totalStates 63 (cachedPairCap 6 1 0))
    (cachedPairMachine 63 6 1 0) _ _ _ _ startB.symm rb
  have runC := retarget_run_first (states:=carriedTailCap 63 1136 6)
    (carriedTailMachine 63 PA17TMDivisionFull012.quotientMachine 6) _ _ _ _ startC.symm rc
  change PSTRTMSeq005.RunsFrom (component (9 : Fin 19)).code _ ta endA at runA
  change PSTRTMSeq005.RunsFrom (component (10 : Fin 19)).code _ tb endB at runB
  change PSTRTMSeq005.RunsFrom (component (11 : Fin 19)).code _ tc endC at runC
  have dA : (component (9 : Fin 19)).decode endA.q=widen64 memory :=
    row64_decode (outerCap 7 allocationK) (carryMachine 63 7 allocationK) memory (outerPort 7 allocationK)
  have dB : (component (10 : Fin 19)).decode endB.q=widen64 memory :=
    row64_decode (cachedPairCap 6 1 0) (cachedPairMachine 63 6 1 0) memory (cachedPairPort 6 1 0)
  have dC : (component (11 : Fin 19)).decode endC.q=widen64 memory :=
    row64_decode (tailCap 1136 6) (carriedTailMachine 63 PA17TMDivisionFull012.quotientMachine 6) memory (tailPort 1136 6)
  have stepA := transfer_to subtract 9 10 (by decide) endA (widen64 memory) (widen64 memory) _ runA.2.2.2 dA rfl rfl rfl
  have stepB := transfer_to subtract 10 11 (by decide) endB (widen64 memory) (widen64 memory) _ runB.2.2.2 dB rfl rfl rfl
  have stepC := transfer_to subtract 11 12 (by decide) endC (widen64 memory) (widen64 memory) _ runC.2.2.2 dC rfl rfl rfl
  have sA := component_segment subtract 9 _ _ _ runA
  have sB := component_segment subtract 10 _ _ _ runB
  have sC := component_segment subtract 11 _ _ _ runC
  have ab := segment_append (addSubMachine subtract) _ _ _ _ _ _ sA sB stepA
  have joined := segment_append (addSubMachine subtract) _ _ _ _ _ _ ab sC stepB
  let trace := (liftTrace (9 : Fin 19) ta++liftTrace (10 : Fin 19) tb)++liftTrace (11 : Fin 19) tc
  refine ⟨gu,trace,liftCfg (11 : Fin 19) endC,lower,upper,joined,stepC,?_⟩
  simp only [trace,List.length_append]
  rw [liftTrace_length (9 : Fin 19) ta,liftTrace_length (10 : Fin 19) tb,liftTrace_length (11 : Fin 19) tc]
  calc
    _ ≤ PA17TMRatArithmeticAddSubBounds073.resourceCoefficient*originalPower x y+
        PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y+
        PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y := Nat.add_le_add (Nat.add_le_add la lb) lc
    _ = _ := by unfold roundCoefficient;ring

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubNormalize077
