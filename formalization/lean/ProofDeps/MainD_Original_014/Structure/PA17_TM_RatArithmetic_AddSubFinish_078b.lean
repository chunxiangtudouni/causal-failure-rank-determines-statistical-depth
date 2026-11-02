module
public import Structure.PA17_TM_RatArithmetic_AddSubFinish_078a

/-! The same075 phases15..18: real U-zero read, actual final workspace,
two-port U/V BReady, real sign dispatch and whole original/cache cleanup.
Both arithmetic modes and every cancellation case use this actual trace. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubFinish078

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticParse002 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticWideCache045
open PA17TMRatArithmeticCachedOuter043 PA17TMRatArithmeticCachedPair054
open PA17TMRatArithmeticNativeTail055 PA17TMRatArithmeticSignedSumFields072
open PA17TMRatArithmeticAddSubBounds073 PA17TMRatArithmeticAddSubController075
open PA17TMRatArithmeticZeroCarry058 (observe_contract observedRecords observeEntry observePort repairedNegative)
open PA17TMRatArithmeticSignDispatch053 (dispatch_canonical_contract dispatchEntry dispatchPort)
open PA17TMRatArithmeticMulClosure059 (bankHeader bankWork allocated_is_work home_is_header)
open PA17TMRatArithmeticMulController057 (widen64 narrow64 narrow_widen allocation128_decode row128_decode)
attribute [local implicit_reducible] totalStates PA17TMRatArithmeticAddSubController075.controllerCap
  PA17TMRatArithmeticCachedOuter043.carryCap PA17TMRatArithmeticCachedPair054.cachedReadyCap
  PA17TMRatArithmeticZeroCarry058.observeCap PA17TMRatArithmeticSignDispatch053.dispatchCap

def finishCoefficient : Nat := resourceCoefficient+3*timeCoefficient

theorem finish_segment (subtract : Bool) (x y : Rat) (gm gn ge gp gq gr gg gu gv : Nat)
    (hM : gm≤2*allocationK*(fieldWidth x y)^2) (hN : gn≤2*allocationK*(fieldWidth x y)^2)
    (hE : ge≤2*allocationK*(fieldWidth x y)^2) (hP : gp≤2*allocationK*(fieldWidth x y)^2)
    (hQ : gq≤2*allocationK*(fieldWidth x y)^2) (hR : gr≤2*allocationK*(fieldWidth x y)^2)
    (hG : gg≤2*allocationK*(fieldWidth x y)^2) (hU : gu≤2*allocationK*(fieldWidth x y)^2)
    (hV : gv≤2*allocationK*(fieldWidth x y)^2) :
    ∃ trace last, PSTRTMSeq005.RunsFrom (addSubMachine subtract)
        (entryCfg (15 : Fin 19) (widen64 (resultMemory subtract x y))
          (lastCacheTape subtract x y gm gn ge gp gq gr gg gu gv)) trace last ∧
      last.Tape=Tape.mk₁ (encode [.rational (target subtract x y)]) ∧
      trace.length≤finishCoefficient*originalPower x y := by
  let m := mRecord x y gm
  let n := nRecord x y gn
  let e := eRecord x y ge
  let p := pRecord x y gp
  let q := qRecord x y gq
  let r := rRecord subtract x y gr
  let g := gRecord subtract x y gg
  let u := uRecord subtract x y gu
  let v := vRecord subtract x y gv
  let oldMemory := resultMemory subtract x y
  let memory := finalMemory subtract x y
  let w := fieldWidth x y
  let gap := allocationK*w^2
  have hw : 1≤w := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  have hgap : 3≤gap := by
    have square : 1≤w^2 := by simpa only [one_pow] using Nat.pow_le_pow_left hw 2
    have scaled := Nat.mul_le_mul_left allocationK square
    have constant : 3≤allocationK := by decide
    dsimp only [gap]
    omega
  have hg : ∀ item∈[m,n,e,p,q,r,g,u,v],item.gap≤2*allocationK*w^2 := by
    intro item hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hM
    · exact hN
    · exact hE
    · exact hP
    · exact hQ
    · exact hR
    · exact hG
    · exact hU
    · exact hV
  obtain ⟨wm,wn,we,wp,wq,wr,wg,wu,wv⟩ := record_widths subtract x y gm gn ge gp gq gr gg gu gv
  have hv : ∀ item∈[m,n,e,p,q,r,g,u,v],item.digits.length≤w := by
    intro item hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact wm
    · exact wn
    · exact we
    · exact wp
    · exact wq
    · exact wr
    · exact wg
    · exact wu
    · exact wv
  obtain ⟨bankGap,bankWidthBound⟩ := cache_totals9 x y [m,n,e,p,q,r,g,u,v] (by change 9≤9;decide) hg hv
  have followingGap : totalGap [v]≤4*allocationK*w^2 := by
    have vGap : v.gap=gv := rfl
    simp only [totalGap,Nat.add_zero,vGap]
    exact hV.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right allocationK (by decide : 2≤4)))
  have followingWidth : totalWidth [v]≤2*w := by
    simp only [totalWidth,Nat.add_zero]
    exact wv.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right w (by decide : 1≤2))
  have sourceWidth : PA17TMRatArithmeticWidth018.bankWidth (false::(numeratorDigits x).tail)
      (false::(denominatorDigits x).tail) (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)≤w := by
    exact (originalWidth_eq x y).le
  have tailWidth : PA17TMRatArithmeticFarLoad031.bankWidth (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail≤w := by
    rw [PA17TMRatArithmeticPairInput050.original_source_width]
  obtain ⟨tr15,run15,len15,_space15⟩ := observe_contract 1 8 oldMemory m [n,e,p,q,r,g] [v] gu
    (quotientNumerator subtract x y) rfl rfl (sign x) [false]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail
  have observedRecordEq : observedRecords [n,e,p,q,r,g] [v] gu (quotientNumerator subtract x y)=[n,e,p,q,r,g,u,v] := rfl
  rw [observedRecordEq,home_is_header] at run15
  change PSTRTMSeq005.RunsFrom (component (15 : Fin 19)).code
    ⟨observeEntry 1 8 oldMemory,lastCacheTape subtract x y gm gn ge gp gq gr gg gu gv⟩ tr15
    ⟨observePort 1 8 memory,bankHeader x y [m,n,e,p,q,r,g,u,v]⟩ at run15
  obtain ⟨tr16,run16,len16,_space16⟩ := actual_allocation_contract9 127 9 memory (by decide)
    [m,n,e,p,q,r,g,u,v] rfl x y hg hv
  rw [allocated_is_work x y m [n,e,p,q,r,g,u,v] gap] at run16
  change PSTRTMSeq005.RunsFrom (component (16 : Fin 19)).code
    ⟨label memory (0 : Fin (outerCap 9 allocationK+1)),bankHeader x y [m,n,e,p,q,r,g,u,v]⟩ tr16
    ⟨(carryFinal 127 9 allocationK memory (bankWork x y m [n,e,p,q,r,g,u,v] gap)).q,
      bankWork x y m [n,e,p,q,r,g,u,v] gap⟩ at run16
  obtain ⟨tr17,run17,len17,_space17⟩ := cached_ready_contract 127 8 1 0 memory m [n,e,p,q,r,g,u,v]
    [m,n,e,p,q,r,g] u [v] [m,n,e,p,q,r,g,u] v [] rfl rfl rfl rfl rfl
    (PA17TMRatArithmeticPairEncode017.payload (quotientNumerator subtract x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator subtract x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (quotientNumerator subtract x y)).tail
    (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator subtract x y)).tail
    (canonical_head_tail _) (canonical_head_tail _) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail gap
  change PSTRTMSeq005.RunsFrom (component (17 : Fin 19)).code
    ⟨label memory (0 : Fin (cachedReadyCap 8 1 0+1)),bankWork x y m [n,e,p,q,r,g,u,v] gap⟩ tr17
    ⟨label memory (cachedReadyPort 8 1 0 (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator subtract x y)).head!),
      originalBReady (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail
        (numeratorDigits y).tail (denominatorDigits y).tail m [n,e,p,q,r,g,u,v] gap
        (PA17TMRatArithmeticPairEncode017.payload (quotientNumerator subtract x y))
        (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator subtract x y))⟩ at run17
  rw [original_ready_final_geometry] at run17
  let readyTape := PA17TMRatArithmeticOutputFinish044.pairInput gap
    (PA17TMRatArithmeticOutputFinish044.latestLeft (sign x) (false::(numeratorDigits x).tail)
      (denominatorDigits x).tail (false::(numeratorDigits y).tail) (denominatorDigits y).tail m [n,e,p,q,r,g,u,v])
    (quotientNumerator subtract x y) (quotientDenominator subtract x y)
  have signProof : repairedNegative memory=decide (target subtract x y<0) := by
    simpa only [sign] using final_output_sign subtract x y
  obtain ⟨tr18,run18,len18,_space18⟩ := dispatch_canonical_contract 8 repairedNegative memory m [n,e,p,q,r,g,u,v] rfl
    (sign x) (false::(numeratorDigits x).tail) (denominatorDigits x).tail
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail gap hgap
    (quotientNumerator subtract x y) (quotientDenominator subtract x y) (target subtract x y)
    (pipeline_fields subtract x y).1 (pipeline_fields subtract x y).2.1 signProof
  change PSTRTMSeq005.RunsFrom (component (18 : Fin 19)).code
    ⟨dispatchEntry 8 memory,readyTape⟩ tr18
    ⟨dispatchPort 8,Tape.mk₁ (encode [.rational (target subtract x y)])⟩ at run18
  have entry15 : (component (15 : Fin 19)).entry (widen64 oldMemory)=observeEntry 1 8 oldMemory := by
    change observeEntry 1 8 (narrow64 (widen64 oldMemory))=_
    rw [narrow_widen]
  have entry16 : (component (16 : Fin 19)).entry memory=label memory (0 : Fin (outerCap 9 allocationK+1)) := rfl
  have entry17 : (component (17 : Fin 19)).entry memory=label memory (0 : Fin (cachedReadyCap 8 1 0+1)) := rfl
  have entry18 : (component (18 : Fin 19)).entry memory=dispatchEntry 8 memory := rfl
  have seg15 := component_segment subtract (15 : Fin 19) _ _ _ run15
  have seg16 := component_segment subtract (16 : Fin 19) _ _ _ run16
  have seg17 := component_segment subtract (17 : Fin 19) _ _ _ run17
  have seg18 := component_segment subtract (18 : Fin 19) _ _ _ run18
  have decode15 : (component (15 : Fin 19)).decode (observePort 1 8 memory)=memory := observer_decode 1 8 memory
  have decode16 : (component (16 : Fin 19)).decode
      (carryFinal 127 9 allocationK memory (bankWork x y m [n,e,p,q,r,g,u,v] gap)).q=memory := allocation128_decode 9 memory _
  have decode17 : (component (17 : Fin 19)).decode
      (label memory (cachedReadyPort 8 1 0 (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator subtract x y)).head!))=memory :=
    row128_decode _ _ memory _
  have step15 := paid_transfer subtract (15 : Fin 19) (by decide) _ run15.2.2.2
  have step16 := paid_transfer subtract (16 : Fin 19) (by decide) _ run16.2.2.2
  have step17 := paid_transfer subtract (17 : Fin 19) (by decide) _ run17.2.2.2
  rw [decode15] at step15
  rw [decode16] at step16
  rw [decode17] at step17
  change TM0.step (addSubMachine subtract) _=some (entryCfg (16 : Fin 19) memory (bankHeader x y [m,n,e,p,q,r,g,u,v])) at step15
  change TM0.step (addSubMachine subtract) _=some (entryCfg (17 : Fin 19) memory (bankWork x y m [n,e,p,q,r,g,u,v] gap)) at step16
  change TM0.step (addSubMachine subtract) _=some (entryCfg (18 : Fin 19) memory readyTape) at step17
  have step15' : TM0.step (addSubMachine subtract) (liftCfg (15 : Fin 19)
      ⟨observePort 1 8 memory,bankHeader x y [m,n,e,p,q,r,g,u,v]⟩)=some (liftCfg (16 : Fin 19)
      ⟨label memory (0 : Fin (outerCap 9 allocationK+1)),bankHeader x y [m,n,e,p,q,r,g,u,v]⟩) := by
    simpa only [entryCfg,entry16] using step15
  have step16' : TM0.step (addSubMachine subtract) (liftCfg (16 : Fin 19)
      ⟨(carryFinal 127 9 allocationK memory (bankWork x y m [n,e,p,q,r,g,u,v] gap)).q,bankWork x y m [n,e,p,q,r,g,u,v] gap⟩)=
      some (liftCfg (17 : Fin 19) ⟨label memory (0 : Fin (cachedReadyCap 8 1 0+1)),bankWork x y m [n,e,p,q,r,g,u,v] gap⟩) := by
    simpa only [entryCfg,entry17] using step16
  have step17' : TM0.step (addSubMachine subtract) (liftCfg (17 : Fin 19)
      ⟨label memory (cachedReadyPort 8 1 0 (PA17TMRatArithmeticPairEncode017.payload (quotientDenominator subtract x y)).head!),readyTape⟩)=
      some (liftCfg (18 : Fin 19) ⟨dispatchEntry 8 memory,readyTape⟩) := by
    simpa only [entryCfg,entry18] using step17
  have joined1516 := segment_append (addSubMachine subtract) _ _ _ _ _ _ seg15 seg16 step15'
  have joined151617 := segment_append (addSubMachine subtract) _ _ _ _ _ _ joined1516 seg17 step16'
  have joined := segment_append (addSubMachine subtract) _ _ _ _ _ _ joined151617 seg18 step17'
  have run := segment_runsFrom (addSubMachine subtract) _ _ _ joined (final_halt subtract _ run18.2.2.2)
  have fee15 := observe_fee9 1 8 (by decide) (by decide) x y m [n,e,p,q,r,g] [v]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) gu (quotientNumerator subtract x y)
    (by simpa only [observedRecordEq] using bankGap) (by simpa only [observedRecordEq] using bankWidthBound)
    followingGap followingWidth (quotient_bits subtract x y).1 sourceWidth
  have fee17 := (cached_fees9 8 1 0 (by decide) x y m [n,e,p,q,r,g,u,v] [m,n,e,p,q,r,g] u [v]
    [m,n,e,p,q,r,g,u] v [] rfl rfl rfl rfl rfl hg hv (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail tailWidth (quotientNumerator subtract x y) (quotientDenominator subtract x y) rfl rfl).2
  have fee18 := output_fee9 8 (by decide) x y m [n,e,p,q,r,g,u,v]
    (false::(numeratorDigits x).tail) (denominatorDigits x).tail
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail gap
    (quotientNumerator subtract x y) (quotientDenominator subtract x y) bankGap bankWidthBound
    sourceWidth (Nat.le_refl _) (by rw [PA17TMRatArithmeticPairEncode017.payload_length];exact (quotient_bits subtract x y).1)
    (by rw [PA17TMRatArithmeticPairEncode017.payload_length];exact (quotient_bits subtract x y).2)
  let trace := ((liftTrace (15 : Fin 19) tr15++liftTrace (16 : Fin 19) tr16)++liftTrace (17 : Fin 19) tr17)++liftTrace (18 : Fin 19) tr18
  have ht15 : (liftTrace (15 : Fin 19) tr15).length=tr15.length := liftTrace_length _ _
  have ht16 : (liftTrace (16 : Fin 19) tr16).length=tr16.length := liftTrace_length _ _
  have ht17 : (liftTrace (17 : Fin 19) tr17).length=tr17.length := liftTrace_length _ _
  have ht18 : (liftTrace (18 : Fin 19) tr18).length=tr18.length := liftTrace_length _ _
  have length : trace.length≤finishCoefficient*originalPower x y := by
    simp only [trace,List.length_append]
    rw [ht15,ht16,ht17,ht18]
    have h15 := len15.trans fee15
    have h17 := len17.trans fee17
    have h18 := len18.trans fee18
    change tr15.length≤timeCoefficient*originalPower x y at h15
    change tr16.length≤resourceCoefficient*originalPower x y at len16
    change tr17.length≤timeCoefficient*originalPower x y at h17
    change tr18.length≤timeCoefficient*originalPower x y at h18
    calc
      _ ≤ ((timeCoefficient*originalPower x y+resourceCoefficient*originalPower x y)+timeCoefficient*originalPower x y)+timeCoefficient*originalPower x y :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h15 len16) h17) h18
      _ = _ := by unfold finishCoefficient;ring
  refine ⟨trace,liftCfg (18 : Fin 19) ⟨dispatchPort 8,Tape.mk₁ (encode [.rational (target subtract x y)])⟩,?_,?_,length⟩
  · have startEq : liftCfg (15 : Fin 19)
        (⟨observeEntry 1 8 oldMemory,lastCacheTape subtract x y gm gn ge gp gq gr gg gu gv⟩ : MachineState (component (15 : Fin 19)).states)=
        entryCfg (15 : Fin 19) (widen64 oldMemory) (lastCacheTape subtract x y gm gn ge gp gq gr gg gu gv) :=
      congrArg (fun stateLabel : Fin ((component (15 : Fin 19)).states+1) =>
        liftCfg (15 : Fin 19) (⟨stateLabel,lastCacheTape subtract x y gm gn ge gp gq gr gg gu gv⟩ : MachineState (component (15 : Fin 19)).states)) entry15.symm
    have originalSegment : Segment (addSubMachine subtract)
        (liftCfg (15 : Fin 19) (⟨observeEntry 1 8 oldMemory,lastCacheTape subtract x y gm gn ge gp gq gr gg gu gv⟩ : MachineState (component (15 : Fin 19)).states)) trace
        (liftCfg (18 : Fin 19) ⟨dispatchPort 8,Tape.mk₁ (encode [.rational (target subtract x y)])⟩) :=
      ⟨run.1,run.2.1,run.2.2.1⟩
    have transported := PA17TMRatArithmeticAddSubPrefix074.retarget_first
      (states:=PA17TMRatArithmeticAddSubController075.controllerCap) (addSubMachine subtract) _ _ _ trace startEq originalSegment
    exact segment_runsFrom (addSubMachine subtract) _ _ _ transported run.2.2.2
  · exact lift_tape (18 : Fin 19) ⟨dispatchPort 8,Tape.mk₁ (encode [.rational (target subtract x y)])⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubFinish078
