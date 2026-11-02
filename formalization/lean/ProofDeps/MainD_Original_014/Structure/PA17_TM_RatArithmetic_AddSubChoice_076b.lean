module
public import Structure.PA17_TM_RatArithmetic_AddSubChoice_076a

/-! Actual allocation, selected Add, and P-zero observation. P is the
earlier saturated difference, NOT the newly produced magnitude R. Its
real observed bit only repairs finite sign control; U-zero is observed later. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubChoice076

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedOuter043
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticMulClosure059 PA17TMRatArithmeticSignedSumFields072
open PA17TMRatArithmeticAddSubController075
open PA17TMRatArithmeticMulController057 (widen64 row64_entry)
attribute [local implicit_reducible] totalStates controllerCap component addRecordComponent
  observerComponent PA17TMRatArithmeticCachedOuter043.carryCap
  PA17TMRatArithmeticZeroCarry058.observeCap
  PA17TMRatArithmeticMulController057.allocation64 PA17TMRatArithmeticMulController057.row64Component

theorem observe_time (mode : Bool) (x y : Rat) (gm gn ge gp gq gr : Nat)
    (hm : gm≤2*allocationK*(fieldWidth x y)^2) (hn : gn≤2*allocationK*(fieldWidth x y)^2)
    (he : ge≤2*allocationK*(fieldWidth x y)^2) (hp : gp≤2*allocationK*(fieldWidth x y)^2)
    (hq : gq≤2*allocationK*(fieldWidth x y)^2) (hr : gr≤2*allocationK*(fieldWidth x y)^2) :
    PA17TMRatArithmeticZeroCarry058.observeFee 2 5 (mRecord x y gm)
      [nRecord x y gn,eRecord x y ge] [qRecord x y gq,rRecord mode x y gr]
      (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) gp (leftDifference x y)≤
        PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y := by
  let records := [mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq,rRecord mode x y gr]
  have hg : ∀ r∈records,r.gap≤2*allocationK*(fieldWidth x y)^2 := by
    intro r h
    simp only [records,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hm
    · exact hn
    · exact he
    · exact hp
    · exact hq
    · exact hr
  obtain ⟨wm,wn,we,wp,wq,wr,_wg,_wu,_wv⟩ := record_widths mode x y gm gn ge gp gq gr 0 0 0
  have hv : ∀ r∈records,r.digits.length≤fieldWidth x y := by
    intro r h
    simp only [records,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    · exact wm
    · exact wn
    · exact we
    · exact wp
    · exact wq
    · exact wr
  obtain ⟨totalG,totalV⟩ := PA17TMRatArithmeticAddSubBounds073.cache_totals9 x y records
    (by change (6 : Nat)≤9;decide) hg hv
  have followingG : totalGap [qRecord x y gq,rRecord mode x y gr]≤4*allocationK*(fieldWidth x y)^2 := by
    calc
      _ ≤ 2*allocationK*(fieldWidth x y)^2+2*allocationK*(fieldWidth x y)^2 := Nat.add_le_add hq hr
      _ = _ := by ring
  have followingV : totalWidth [qRecord x y gq,rRecord mode x y gr]≤2*fieldWidth x y := by
    calc
      _ ≤ fieldWidth x y+fieldWidth x y := Nat.add_le_add wq wr
      _ = _ := by ring
  exact PA17TMRatArithmeticAddSubBounds073.observe_fee9 2 5 (by decide) (by decide) x y
    (mRecord x y gm) [nRecord x y gn,eRecord x y ge] [qRecord x y gq,rRecord mode x y gr]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) gp (leftDifference x y)
    totalG totalV followingG followingV (difference_bits x y).1
    (PA17TMRatArithmeticWidth018.originalWidth_eq x y).le

/-- A fixed mode precedes all actual operands. Five bounds below are
internal native-producer invariants. The source zero bit is really read by
058 from P, and only the paid outgoing transition installs resultMemory. -/
theorem choice_segment (mode : Bool) (x y : Rat) (gm gn ge gp gq : Nat)
    (hm : gm≤2*allocationK*(fieldWidth x y)^2) (hn : gn≤2*allocationK*(fieldWidth x y)^2)
    (he : ge≤2*allocationK*(fieldWidth x y)^2) (hp : gp≤2*allocationK*(fieldWidth x y)^2)
    (hq : gq≤2*allocationK*(fieldWidth x y)^2) :
    ∃ gr trace last, 6≤gr ∧ gr≤2*allocationK*(fieldWidth x y)^2 ∧
      Segment (addSubMachine mode)
        (entryCfg (1 : Fin 19) (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y))
          (PA17TMRatArithmeticAddSubPrefix074.postTape x y gm gn ge gp gq)) trace last ∧
      TM0.step (addSubMachine mode) last=some
        (entryCfg (6 : Fin 19) (widen64 (resultMemory mode x y))
          (bankHeader x y [mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq,rRecord mode x y gr])) ∧
      trace.length≤choiceCoefficient*originalPower x y := by
  let memory := PA17TMRatArithmeticMulStart049.actualMemory x y
  let m := mRecord x y gm
  let later := [nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq]
  let gap := freshGap x y
  let a := addLeft mode x y
  let b := addRight mode x y
  have hg := five_gap_bounds x y gm gn ge gp gq hm hn he hp hq
  have hv := five_width_bounds mode x y gm gn ge gp gq
  obtain ⟨t1,r1,len1,_space1⟩ := PA17TMRatArithmeticAddSubBounds073.actual_allocation_contract9 63 5 memory
    (by decide) (m::later) rfl x y hg hv
  rw [allocated_is_work x y m later (allocationK*(fieldWidth x y)^2)] at r1
  let first1 : MachineState (component (1 : Fin 19)).states :=
    ⟨(component (1 : Fin 19)).entry (widen64 memory),bankHeader x y (m::later)⟩
  let last1 : MachineState (PA17TMRatArithmeticCachedOuter043.carryCap 63 5 allocationK) :=
    carryFinal 63 5 allocationK memory (bankWork x y m later gap)
  have start1 : first1=carryEntry 63 5 allocationK memory (bankHeader x y (m::later)) :=
    row_entry_cfg (outerCap 5 allocationK) (carryMachine 63 5 allocationK) memory _
  have run1 : PSTRTMSeq005.RunsFrom (component (1 : Fin 19)).code first1 t1 last1 :=
    ⟨r1.1.trans (congrArg some start1.symm),r1.2.1,r1.2.2.1,r1.2.2.2⟩
  have decode1 : (component (1 : Fin 19)).decode last1.q=widen64 memory :=
    PA17TMRatArithmeticMulController057.row64_decode (outerCap 5 allocationK)
      (carryMachine 63 5 allocationK) memory (outerPort 5 allocationK)
  have step1 := transfer_to mode (1 : Fin 19) (selectedPairPhase mode x y) (by decide) last1
    (widen64 memory) (widen64 memory) (bankWork x y m later gap) run1.2.2.2 decode1
    (selected_phase_actual mode x y) rfl rfl
  have segment1 := component_segment mode (1 : Fin 19) _ _ _ run1
  obtain ⟨tp,lastP,segmentP,stepP,lenP⟩ := selected_pair_segment mode x y gm gn ge gp gq hg
  have joined1P := segment_append (addSubMachine mode) _ _ _ _ _ _ segment1 segmentP step1
  obtain ⟨_s1,_s2,_s3,_s4,_s5,scaleAdd,_s7,_s8,_s9⟩ := nine_scales mode x y
  let archive := true::lastArchive (sign x) [false] (false::(numeratorDigits x).tail)
    (false::(denominatorDigits x).tail) (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m later
  obtain ⟨gr,ta,lastA,ra,wholeA,lowerR,upperR,lenA,_spaceA⟩ :=
    add_allocated_runsFrom a b (fieldWidth x y) archive (original_width_positive x y) scaleAdd
  have boundR := new_gap_bound a b (fieldWidth x y) gr (original_width_positive x y) scaleAdd upperR
  let r := rRecord mode x y gr
  let header6 := bankHeader x y (m::(later++[r]))
  let observedInput := PA17TMRatArithmeticReturnHome037.homeInput (sign x) [false]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m (later++[r]) []
  have sumEq : a+b=sumMagnitude mode x y := add_arguments_sum mode x y
  have output : lastA.Tape=observedInput := by
    have h := wholeA.trans (newRecord_home (sign x) [false] (false::(numeratorDigits x).tail)
      (false::(denominatorDigits x).tail) (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail)
      m later gr (a+b))
    rw [sumEq] at h
    exact h
  let endA : MachineState 503 := ⟨lastA.q,observedInput⟩
  have lastEq : lastA=endA := by
    cases lastA with
    | mk q tape => exact congrArg (fun t : Tape Bool => (⟨q,t⟩ : MachineState 503)) output
  rw [lastEq] at ra
  change PSTRTMSeq005.RunsFrom PA17TMRatArithmeticNativeCache030.addCacheMachine
    (⟨0,tailInput (sign x) [false] (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m later gap a b⟩ : MachineState 503) ta endA at ra
  rw [←native_is_tail_input x y m later gap a b] at ra
  have r4 := add_record_runs memory _ _ ta ra
  let t4 := ta.map (blockCfg (s:=503) memory)
  let first4 : MachineState (component (4 : Fin 19)).states :=
    ⟨(component (4 : Fin 19)).entry (widen64 memory),bankNative x y m later gap a b⟩
  let last4 : MachineState (totalStates 63 503) := blockCfg memory endA
  have start4 : first4=blockCfg memory (⟨0,bankNative x y m later gap a b⟩ : MachineState 503) :=
    row_entry_cfg 503 addRecordMachine memory _
  have run4 : PSTRTMSeq005.RunsFrom (component (4 : Fin 19)).code first4 t4 last4 :=
    ⟨r4.1.trans (congrArg some start4.symm),r4.2.1,r4.2.2.1,r4.2.2.2⟩
  have decode4 : (component (4 : Fin 19)).decode last4.q=widen64 memory := add_record_decode memory endA.q
  have step4 := transfer_to mode (4 : Fin 19) 5 (by decide) last4 (widen64 memory) (widen64 memory)
    observedInput run4.2.2.2 decode4 rfl rfl rfl
  have segment4 := component_segment mode (4 : Fin 19) _ _ _ run4
  have joined1P4 := segment_append (addSubMachine mode) _ lastP _ _ _ _ joined1P segment4 stepP
  let selected := PA17TMRatArithmeticZeroCarry058.observedMemory memory (decide (leftDifference x y=0))
  obtain ⟨t5,r5,len5,_space5⟩ := PA17TMRatArithmeticZeroCarry058.observe_contract 2 5 memory
    m [nRecord x y gn,eRecord x y ge] [qRecord x y gq,r] gp (leftDifference x y) rfl rfl (sign x) [false]
    (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
    (false::(numeratorDigits y).tail) (denominatorDigits y).tail
  let first5 : MachineState (PA17TMRatArithmeticZeroCarry058.observeCap 2 5) :=
    ⟨PA17TMRatArithmeticZeroCarry058.observeEntry 2 5 memory,observedInput⟩
  let last5 : MachineState (PA17TMRatArithmeticZeroCarry058.observeCap 2 5) :=
    ⟨PA17TMRatArithmeticZeroCarry058.observePort 2 5 selected,header6⟩
  have start5 : (⟨(component (5 : Fin 19)).entry (widen64 memory),observedInput⟩ :
      MachineState (PA17TMRatArithmeticZeroCarry058.observeCap 2 5))=first5 := by
    change (⟨PA17TMRatArithmeticZeroCarry058.observeEntry 2 5
      (PA17TMRatArithmeticMulController057.narrow64 (widen64 memory)),observedInput⟩ :
      MachineState (PA17TMRatArithmeticZeroCarry058.observeCap 2 5))=first5
    rw [PA17TMRatArithmeticMulController057.narrow_widen]
  have run5 : PSTRTMSeq005.RunsFrom (component (5 : Fin 19)).code
      ⟨(component (5 : Fin 19)).entry (widen64 memory),observedInput⟩ t5 last5 :=
    ⟨r5.1.trans (congrArg some start5.symm),r5.2.1,r5.2.2.1,r5.2.2.2⟩
  have decode5 : (component (5 : Fin 19)).decode last5.q=selected := observer_decode 2 5 selected
  have remap : nextMemory mode (5 : Fin 19) selected=widen64 (resultMemory mode x y) :=
    observed_sign_transfer mode memory (decide (leftDifference x y=0))
  have step5 := transfer_to mode (5 : Fin 19) 6 (by decide) last5 selected
    (widen64 (resultMemory mode x y)) header6 run5.2.2.2 decode5 rfl remap rfl
  have segment5 := component_segment mode (5 : Fin 19) _ _ _ run5
  have joined := segment_append (addSubMachine mode) _ (liftCfg (4 : Fin 19) last4) _ _ _ _ joined1P4 segment5 step4
  have feeA := lenA.trans (PA17TMRatArithmeticAddSubBounds073.native_record_fee9 x y a b scaleAdd)
  have fee5 := len5.trans (observe_time mode x y gm gn ge gp gq gr hm hn he hp hq boundR)
  refine ⟨gr,((liftTrace (1 : Fin 19) t1++tp)++liftTrace (4 : Fin 19) t4)++liftTrace (5 : Fin 19) t5,
    liftCfg (5 : Fin 19) last5,lowerR,boundR,joined,step5,?_⟩
  have l1 : (liftTrace (1 : Fin 19) t1).length=t1.length := liftTrace_length _ _
  have l4 : (liftTrace (4 : Fin 19) t4).length=t4.length := liftTrace_length _ _
  have l5 : (liftTrace (5 : Fin 19) t5).length=t5.length := liftTrace_length _ _
  have mapLength : t4.length=ta.length := List.length_map _
  have fee4 : t4.length≤PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y := mapLength.trans_le feeA
  rw [List.length_append,List.length_append,List.length_append,l1,l4,l5]
  calc
    _ ≤ ((PA17TMRatArithmeticAddSubBounds073.resourceCoefficient*originalPower x y+
        PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y)+
        PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y)+
        PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add len1 lenP) fee4) fee5
    _ = _ := by unfold choiceCoefficient;ring

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubChoice076
