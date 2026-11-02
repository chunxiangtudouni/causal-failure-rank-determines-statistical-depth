module
public import Structure.PA17_TM_RatArithmetic_AddSubController_075b
public import Structure.PA17_TM_RatArithmetic_AddSubBounds_073a
public import Structure.PA17_TM_RatArithmetic_MulClosure_059b
public import Structure.PA17_TM_RatArithmetic_MulController_057a

/-! Execute the unchanged075 phases12..14. V is genuinely stored and the
last local HALT really transfers to the U-zero observer at phase15. There
is no inserted phase15 singleton or uncharged returnHome for V. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubFinish078

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticParse002 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticWideCache045
open PA17TMRatArithmeticCachedOuter043 PA17TMRatArithmeticCachedPair054
open PA17TMRatArithmeticNativeTail055 PA17TMRatArithmeticNativeCache030
open PA17TMRatArithmeticSignedSumFields072 PA17TMRatArithmeticAddSubBounds073
open PA17TMRatArithmeticAddSubController075
open PA17TMRatArithmeticMulClosure059 (bankHeader bankWork bankNative allocated_is_work
  native_is_tail_input home_is_header)
open PA17TMRatArithmeticMulController057 (widen64 narrow64 row64_entry
  allocation64_decode allocation128_decode cached_decode quotient_record_runs quotient_record_decode row128_decode)
attribute [local implicit_reducible] totalStates PA17TMRatArithmeticAddSubController075.controllerCap
  PA17TMRatArithmeticCachedOuter043.carryCap PA17TMRatArithmeticCachedPair054.cachedPairCap

def vCoefficient : Nat := resourceCoefficient+2*timeCoefficient

def lastCacheTape (subtract : Bool) (x y : Rat) (gm gn ge gp gq gr gg gu gv : Nat) : Tape Bool :=
  PA17TMRatArithmeticReturnHome037.homeInput (sign x) [false]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
    (mRecord x y gm) [nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq,
      rRecord subtract x y gr,gRecord subtract x y gg,uRecord subtract x y gu,vRecord subtract x y gv] []

theorem v_segment (subtract : Bool) (x y : Rat) (gm gn ge gp gq gr gg gu : Nat)
    (hM : gm≤2*allocationK*(fieldWidth x y)^2) (hN : gn≤2*allocationK*(fieldWidth x y)^2)
    (hE : ge≤2*allocationK*(fieldWidth x y)^2) (hP : gp≤2*allocationK*(fieldWidth x y)^2)
    (hQ : gq≤2*allocationK*(fieldWidth x y)^2) (hR : gr≤2*allocationK*(fieldWidth x y)^2)
    (hG : gg≤2*allocationK*(fieldWidth x y)^2) (hU : gu≤2*allocationK*(fieldWidth x y)^2) :
    ∃ gv trace last, 6≤gv ∧ gv≤2*allocationK*(fieldWidth x y)^2 ∧
      Segment (addSubMachine subtract)
        (entryCfg (12 : Fin 19) (widen64 (resultMemory subtract x y))
          (bankHeader x y [mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq,
            rRecord subtract x y gr,gRecord subtract x y gg,uRecord subtract x y gu])) trace last ∧
      TM0.step (addSubMachine subtract) last=some
        (entryCfg (15 : Fin 19) (widen64 (resultMemory subtract x y))
          (lastCacheTape subtract x y gm gn ge gp gq gr gg gu gv)) ∧
      trace.length≤vCoefficient*originalPower x y := by
  let m := mRecord x y gm
  let n := nRecord x y gn
  let e := eRecord x y ge
  let p := pRecord x y gp
  let q := qRecord x y gq
  let r := rRecord subtract x y gr
  let g := gRecord subtract x y gg
  let u := uRecord subtract x y gu
  let memory := resultMemory subtract x y
  let w := fieldWidth x y
  let gap := allocationK*w^2
  have hw : 1≤w := by have h:=PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y;omega
  obtain ⟨_,_,_,_,_,_,_,_,hscale⟩ := nine_scales subtract x y
  have hg : ∀ item∈[m,n,e,p,q,r,g,u],item.gap≤2*allocationK*w^2 := by
    intro item hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hM
    · exact hN
    · exact hE
    · exact hP
    · exact hQ
    · exact hR
    · exact hG
    · exact hU
  have hv : ∀ item∈[m,n,e,p,q,r,g,u],item.digits.length≤w := by
    obtain ⟨wm,wn,we,wp,wq,wr,wg,wu,_⟩ := record_widths subtract x y gm gn ge gp gq gr gg gu 0
    intro item hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact wm
    · exact wn
    · exact we
    · exact wp
    · exact wq
    · exact wr
    · exact wg
    · exact wu
  obtain ⟨tr12,run12,len12,_space12⟩ := actual_allocation_contract9 63 8 memory (by decide)
    [m,n,e,p,q,r,g,u] rfl x y hg hv
  rw [allocated_is_work x y m [n,e,p,q,r,g,u] gap] at run12
  change PSTRTMSeq005.RunsFrom (component (12 : Fin 19)).code
    ⟨label memory (0 : Fin (outerCap 8 allocationK+1)),bankHeader x y [m,n,e,p,q,r,g,u]⟩ tr12
    ⟨(carryFinal 63 8 allocationK memory (bankWork x y m [n,e,p,q,r,g,u] gap)).q,
      bankWork x y m [n,e,p,q,r,g,u] gap⟩ at run12
  obtain ⟨tr13,run13,len13,_space13⟩ := cached_pair_contract 63 7 5 1 memory m [n,e,p,q,r,g,u]
    [m,n] e [p,q,r,g,u] [m,n,e,p,q,r] g [u] rfl rfl rfl rfl rfl
    (PA17TMRatArithmeticPairEncode017.payload (commonDenominator x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (normalizer subtract x y)).head!
    (PA17TMRatArithmeticPairEncode017.payload (commonDenominator x y)).tail
    (PA17TMRatArithmeticPairEncode017.payload (normalizer subtract x y)).tail
    (canonical_head_tail _) (canonical_head_tail _) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    gap (commonDenominator x y) (normalizer subtract x y) rfl rfl
  change PSTRTMSeq005.RunsFrom (component (13 : Fin 19)).code
    ⟨label memory (0 : Fin (cachedPairCap 7 5 1+1)),bankWork x y m [n,e,p,q,r,g,u] gap⟩ tr13
    ⟨label memory (cachedPairPort 7 5 1),bankNative x y m [n,e,p,q,r,g,u] gap
      (commonDenominator x y) (normalizer subtract x y)⟩ at run13
  have actual := quotient_allocated_runsFrom (commonDenominator x y) (normalizer subtract x y) w
    (true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [n,e,p,q,r,g,u]) hw hscale
  obtain ⟨gv,trLocal,lastLocal,runLocal,lastTape,lower,upper,lenLocal,_spaceLocal⟩ := actual
  let output := lastCacheTape subtract x y gm gn ge gp gq gr gg gu gv
  have lastTape' : lastLocal.Tape=output := lastTape.trans
    (newRecord_home (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [n,e,p,q,r,g,u] gv
      (quotientDenominator subtract x y))
  have lastEq : lastLocal=⟨lastLocal.q,output⟩ := by
    cases lastLocal with
    | mk q tape => exact congrArg (fun t => (⟨q,t⟩ : MachineState 1170)) lastTape'
  change PSTRTMSeq005.RunsFrom quotientCacheMachine
    ⟨0,tailInput (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [n,e,p,q,r,g,u]
      gap (commonDenominator x y) (normalizer subtract x y)⟩ trLocal lastLocal at runLocal
  rw [←native_is_tail_input,lastEq] at runLocal
  have run14 := quotient_record_runs memory _ _ _ runLocal
  let tr14 := trLocal.map (blockCfg (p:=63) (s:=1170) memory)
  change PSTRTMSeq005.RunsFrom (component (14 : Fin 19)).code
    ⟨label memory (0 : Fin 1171),bankNative x y m [n,e,p,q,r,g,u] gap
      (commonDenominator x y) (normalizer subtract x y)⟩ tr14 ⟨label memory lastLocal.q,output⟩ at run14
  have gvBound : gv≤2*allocationK*w^2 := new_gap_bound _ _ w gv hw hscale upper
  have entry12 : (component (12 : Fin 19)).entry (widen64 memory)=label memory (0 : Fin (outerCap 8 allocationK+1)) := row64_entry _ _ memory
  have entry13 : (component (13 : Fin 19)).entry (widen64 memory)=label memory (0 : Fin (cachedPairCap 7 5 1+1)) := row64_entry _ _ memory
  have entry14 : (component (14 : Fin 19)).entry (widen64 memory)=label memory (0 : Fin 1171) := row64_entry _ _ memory
  have seg12 := component_segment subtract (12 : Fin 19) _ _ _ run12
  have seg13 := component_segment subtract (13 : Fin 19) _ _ _ run13
  have seg14 := component_segment subtract (14 : Fin 19) _ _ _ run14
  have decode12 : (component (12 : Fin 19)).decode
      (carryFinal 63 8 allocationK memory (bankWork x y m [n,e,p,q,r,g,u] gap)).q=widen64 memory := allocation64_decode 8 memory _
  have decode13 : (component (13 : Fin 19)).decode (label memory (cachedPairPort 7 5 1))=widen64 memory := cached_decode 7 5 1 memory
  have decode14 : (component (14 : Fin 19)).decode (label memory lastLocal.q)=widen64 memory := quotient_record_decode memory lastLocal.q
  have step12 := paid_transfer subtract (12 : Fin 19) (by decide) _ run12.2.2.2
  have step13 := paid_transfer subtract (13 : Fin 19) (by decide) _ run13.2.2.2
  have step14 := paid_transfer subtract (14 : Fin 19) (by decide) _ run14.2.2.2
  rw [decode12] at step12
  rw [decode13] at step13
  rw [decode14] at step14
  change TM0.step (addSubMachine subtract) _=some (entryCfg (13 : Fin 19) (widen64 memory) (bankWork x y m [n,e,p,q,r,g,u] gap)) at step12
  change TM0.step (addSubMachine subtract) _=some (entryCfg (14 : Fin 19) (widen64 memory)
    (bankNative x y m [n,e,p,q,r,g,u] gap (commonDenominator x y) (normalizer subtract x y))) at step13
  change TM0.step (addSubMachine subtract) _=some (entryCfg (15 : Fin 19) (widen64 memory) output) at step14
  have step12' : TM0.step (addSubMachine subtract) (liftCfg (12 : Fin 19)
      ⟨(carryFinal 63 8 allocationK memory (bankWork x y m [n,e,p,q,r,g,u] gap)).q,bankWork x y m [n,e,p,q,r,g,u] gap⟩)=
      some (liftCfg (13 : Fin 19) ⟨label memory (0 : Fin (cachedPairCap 7 5 1+1)),bankWork x y m [n,e,p,q,r,g,u] gap⟩) := by
    simpa only [entryCfg,entry13] using step12
  have step13' : TM0.step (addSubMachine subtract) (liftCfg (13 : Fin 19)
      ⟨label memory (cachedPairPort 7 5 1),bankNative x y m [n,e,p,q,r,g,u] gap (commonDenominator x y) (normalizer subtract x y)⟩)=
      some (liftCfg (14 : Fin 19) ⟨label memory (0 : Fin 1171),bankNative x y m [n,e,p,q,r,g,u] gap
        (commonDenominator x y) (normalizer subtract x y)⟩) := by
    simpa only [entryCfg,entry14] using step13
  have joined := segment_append (addSubMachine subtract) _ _ _ _ _ _
    (segment_append (addSubMachine subtract) _ _ _ _ _ _ seg12 seg13 step12') seg14 step13'
  have sourceWidth : PA17TMRatArithmeticFarLoad031.bankWidth (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail≤fieldWidth x y := by rw [PA17TMRatArithmeticPairInput050.original_source_width]
  have fee13 := (cached_fees9 7 5 1 (by decide) x y m [n,e,p,q,r,g,u] [m,n] e [p,q,r,g,u]
    [m,n,e,p,q,r] g [u] rfl rfl rfl rfl rfl hg hv (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail sourceWidth (commonDenominator x y) (normalizer subtract x y) rfl rfl).1
  have fee14 := native_record_fee9 x y (commonDenominator x y) (normalizer subtract x y) hscale
  let trace := (liftTrace (12 : Fin 19) tr12++liftTrace (13 : Fin 19) tr13)++liftTrace (14 : Fin 19) tr14
  have ht12 : (liftTrace (12 : Fin 19) tr12).length=tr12.length := liftTrace_length _ _
  have ht13 : (liftTrace (13 : Fin 19) tr13).length=tr13.length := liftTrace_length _ _
  have ht14 : (liftTrace (14 : Fin 19) tr14).length=tr14.length := liftTrace_length _ _
  have length : trace.length≤vCoefficient*originalPower x y := by
    simp only [trace,List.length_append]
    rw [ht12,ht13,ht14]
    have h13 := len13.trans fee13
    have h14 : tr14.length≤timeCoefficient*originalPower x y := by
      simp only [tr14,List.length_map]
      exact lenLocal.trans fee14
    change tr12.length≤resourceCoefficient*originalPower x y at len12
    change tr13.length≤timeCoefficient*originalPower x y at h13
    calc
      _ ≤ resourceCoefficient*originalPower x y+timeCoefficient*originalPower x y+timeCoefficient*originalPower x y :=
        Nat.add_le_add (Nat.add_le_add len12 h13) h14
      _ = _ := by unfold vCoefficient;ring
  have startEq : liftCfg (12 : Fin 19)
      (⟨label memory (0 : Fin (outerCap 8 allocationK+1)),bankHeader x y [m,n,e,p,q,r,g,u]⟩ : MachineState (component (12 : Fin 19)).states)=
      entryCfg (12 : Fin 19) (widen64 memory) (bankHeader x y [m,n,e,p,q,r,g,u]) :=
    congrArg (fun stateLabel : Fin ((component (12 : Fin 19)).states+1) =>
      liftCfg (12 : Fin 19) (⟨stateLabel,bankHeader x y [m,n,e,p,q,r,g,u]⟩ : MachineState (component (12 : Fin 19)).states)) entry12.symm
  refine ⟨gv,trace,liftCfg (14 : Fin 19) (⟨label memory lastLocal.q,output⟩ : MachineState (component (14 : Fin 19)).states),
    lower,gvBound,?_,step14,length⟩
  exact PA17TMRatArithmeticAddSubPrefix074.retarget_first
    (states:=PA17TMRatArithmeticAddSubController075.controllerCap) (addSubMachine subtract) _ _ _ trace startEq joined

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubFinish078
