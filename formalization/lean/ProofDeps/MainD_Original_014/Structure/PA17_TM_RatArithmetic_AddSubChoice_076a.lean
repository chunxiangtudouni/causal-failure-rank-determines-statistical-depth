module
public import Structure.PA17_TM_RatArithmetic_AddSubController_075b
public import Structure.PA17_TM_RatArithmetic_AddSubBounds_073a
public import Structure.PA17_TM_RatArithmetic_MulClosure_059b

/-! Real selected cached-pair preparation for fixed Add/Sub code. M/N are
chosen for equal effective signs; the TWO actual saturated differences P/Q
are chosen otherwise. No host bit selects executable code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubChoice076

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticWidth018 (originalBank prefixRight)
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedPair054
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticMulClosure059 PA17TMRatArithmeticSignedSumFields072
open PA17TMRatArithmeticMulController057 (widen64 row64Component row64_entry row64_decode)
open PA17TMRatArithmeticAddSubController075
attribute [local implicit_reducible] totalStates cachedPairCap controllerCap component
  PA17TMRatArithmeticMulController057.cached64 row64Component

def freshGap (x y : Rat) : Nat := allocationK*(fieldWidth x y)^2
def selectedPairPhase (mode : Bool) (x y : Rat) : Fin 19 := if sameSigns mode x y then 2 else 3
def choiceCoefficient : Nat := PA17TMRatArithmeticAddSubBounds073.resourceCoefficient+
  3*PA17TMRatArithmeticAddSubBounds073.timeCoefficient

theorem choiceCoefficient_pos : 0<choiceCoefficient := by
  have h := PA17TMRatArithmeticAddSubBounds073.coefficients_pos
  unfold choiceCoefficient
  omega

theorem original_width_positive (x y : Rat) : 1≤fieldWidth x y :=
  (by decide : (1 : Nat)≤4).trans (PA17TMRatArithmeticMulFields048.fieldWidth_ge_four x y)

theorem five_gap_bounds (x y : Rat) (gm gn ge gp gq : Nat)
    (hm : gm≤2*allocationK*(fieldWidth x y)^2) (hn : gn≤2*allocationK*(fieldWidth x y)^2)
    (he : ge≤2*allocationK*(fieldWidth x y)^2) (hp : gp≤2*allocationK*(fieldWidth x y)^2)
    (hq : gq≤2*allocationK*(fieldWidth x y)^2) :
    ∀ r∈[mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq],
      r.gap≤2*allocationK*(fieldWidth x y)^2 := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact hm
  · exact hn
  · exact he
  · exact hp
  · exact hq

theorem five_width_bounds (mode : Bool) (x y : Rat) (gm gn ge gp gq : Nat) :
    ∀ r∈[mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq],
      r.digits.length≤fieldWidth x y := by
  obtain ⟨hm,hn,he,hp,hq,_hr,_hg,_hu,_hv⟩ := record_widths mode x y gm gn ge gp gq 0 0 0 0
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact hm
  · exact hn
  · exact he
  · exact hp
  · exact hq

theorem selected_phase_actual (mode : Bool) (x y : Rat) :
    nextPhase mode (1 : Fin 19) (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y))=
      selectedPairPhase mode x y := by
  rw [selected_pair_phase,actual_sameSigns]
  rfl

theorem add_arguments_sum (mode : Bool) (x y : Rat) :
    addLeft mode x y+addRight mode x y=sumMagnitude mode x y := by
  cases hs : sameSigns mode x y <;>
    simp only [addLeft,addRight,sumMagnitude,hs,ite_true,Bool.false_eq_true,ite_false]

theorem row_entry_cfg (states : Nat) (code : Machine (totalStates 63 states))
    (memory : Fin 64) (tape : Tape Bool) :
    (⟨(row64Component states code).entry (widen64 memory),tape⟩ : MachineState (totalStates 63 states))=
      blockCfg memory (⟨0,tape⟩ : MachineState states) := by
  rw [row64_entry]
  rfl

theorem cached_data (mode : Bool) (x y : Rat) (gm gn ge gp gq aLater bLater : Nat)
    (hg : ∀ r∈[mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq],
      r.gap≤2*allocationK*(fieldWidth x y)^2)
    (beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec)
    (hbankA : beforeA++sourceA::followingA=[mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq])
    (hA : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=[mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq])
    (hB : followingB.length=bLater) (a b : Nat)
    (ha : sourceA.digits=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : sourceB.digits=PA17TMRatArithmeticPairEncode017.payload b) :
    ∃ trace, PSTRTMSeq005.RunsFrom (cachedPairMachine 63 4 aLater bLater)
      (blockCfg (PA17TMRatArithmeticMulStart049.actualMemory x y)
        (⟨0,bankWork x y (mRecord x y gm) [nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq]
          (freshGap x y)⟩ : MachineState (cachedPairCap 4 aLater bLater))) trace
      (blockCfg (PA17TMRatArithmeticMulStart049.actualMemory x y)
        (⟨cachedPairPort 4 aLater bLater,bankNative x y (mRecord x y gm)
          [nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq] (freshGap x y) a b⟩ :
          MachineState (cachedPairCap 4 aLater bLater))) ∧
      trace.length≤PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y := by
  obtain ⟨trace,run,time,_space⟩ := cached_pair_contract 63 4 aLater bLater
    (PA17TMRatArithmeticMulStart049.actualMemory x y) (mRecord x y gm)
    [nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq]
    beforeA sourceA followingA beforeB sourceB followingB rfl hbankA hA hbankB hB
    (PA17TMRatArithmeticPairEncode017.payload a).head! (PA17TMRatArithmeticPairEncode017.payload b).head!
    (PA17TMRatArithmeticPairEncode017.payload a).tail (PA17TMRatArithmeticPairEncode017.payload b).tail
    (ha.trans (canonical_head_tail a)) (hb.trans (canonical_head_tail b)) (sign x) [false]
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    (freshGap x y) a b ha hb
  have fee := (PA17TMRatArithmeticAddSubBounds073.cached_fees9 4 aLater bLater (by decide) x y
    (mRecord x y gm) [nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq]
    beforeA sourceA followingA beforeB sourceB followingB rfl hbankA hA hbankB hB hg
    (five_width_bounds mode x y gm gn ge gp gq)
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    (PA17TMRatArithmeticPairInput050.original_source_width x y).le a b ha hb).1
  exact ⟨trace,run,time.trans fee⟩

/-- The phase in this proof describes the actual finite sign-table branch.
The caller supplies its real paid phase1 step, not a caller-provided flag. -/
theorem selected_pair_segment (mode : Bool) (x y : Rat) (gm gn ge gp gq : Nat)
    (hg : ∀ r∈[mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq],
      r.gap≤2*allocationK*(fieldWidth x y)^2) :
    ∃ trace last, Segment (addSubMachine mode)
      (entryCfg (selectedPairPhase mode x y) (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y))
        (bankWork x y (mRecord x y gm) [nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq] (freshGap x y)))
      trace last ∧ TM0.step (addSubMachine mode) last=some
        (entryCfg (4 : Fin 19) (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y))
          (bankNative x y (mRecord x y gm) [nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq]
            (freshGap x y) (addLeft mode x y) (addRight mode x y))) ∧
      trace.length≤PA17TMRatArithmeticAddSubBounds073.timeCoefficient*originalPower x y := by
  let memory := PA17TMRatArithmeticMulStart049.actualMemory x y
  let m := mRecord x y gm
  let later := [nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq]
  cases hs : sameSigns mode x y <;>
    simp only [selectedPairPhase,addLeft,addRight,hs,ite_true,Bool.false_eq_true,ite_false]
  · obtain ⟨tr,run,len⟩ := cached_data mode x y gm gn ge gp gq 1 0 hg
      [mRecord x y gm,nRecord x y gn,eRecord x y ge] (pRecord x y gp) [qRecord x y gq]
      [mRecord x y gm,nRecord x y gn,eRecord x y ge,pRecord x y gp] (qRecord x y gq) []
      rfl rfl rfl rfl (leftDifference x y) (rightDifference x y) rfl rfl
    let first : MachineState (component (3 : Fin 19)).states :=
      ⟨(component (3 : Fin 19)).entry (widen64 memory),bankWork x y m later (freshGap x y)⟩
    let last : MachineState (totalStates 63 (cachedPairCap 4 1 0)) := blockCfg memory
      (⟨cachedPairPort 4 1 0,bankNative x y m later (freshGap x y) (leftDifference x y) (rightDifference x y)⟩ :
        MachineState (cachedPairCap 4 1 0))
    have start : first=blockCfg memory (⟨0,bankWork x y m later (freshGap x y)⟩ : MachineState (cachedPairCap 4 1 0)) :=
      row_entry_cfg (cachedPairCap 4 1 0) (cachedPairMachine 63 4 1 0) memory
        (bankWork x y m later (freshGap x y))
    have actual : PSTRTMSeq005.RunsFrom (component (3 : Fin 19)).code first tr last :=
      ⟨run.1.trans (congrArg some start.symm),run.2.1,run.2.2.1,run.2.2.2⟩
    have decoded : (component (3 : Fin 19)).decode last.q=widen64 memory :=
      row64_decode (cachedPairCap 4 1 0) (cachedPairMachine 63 4 1 0) memory (cachedPairPort 4 1 0)
    have step := transfer_to mode (3 : Fin 19) 4 (by decide) last (widen64 memory) (widen64 memory)
      last.Tape actual.2.2.2 decoded rfl rfl rfl
    have segment := component_segment mode (3 : Fin 19) _ _ _ actual
    refine ⟨liftTrace (3 : Fin 19) tr,liftCfg (3 : Fin 19) last,segment,step,?_⟩
    exact (liftTrace_length (3 : Fin 19) tr).trans_le len
  · obtain ⟨tr,run,len⟩ := cached_data mode x y gm gn ge gp gq 4 3 hg
      [] (mRecord x y gm) [nRecord x y gn,eRecord x y ge,pRecord x y gp,qRecord x y gq]
      [mRecord x y gm] (nRecord x y gn) [eRecord x y ge,pRecord x y gp,qRecord x y gq]
      rfl rfl rfl rfl (leftMagnitude x y) (rightMagnitude x y) rfl rfl
    let first : MachineState (component (2 : Fin 19)).states :=
      ⟨(component (2 : Fin 19)).entry (widen64 memory),bankWork x y m later (freshGap x y)⟩
    let last : MachineState (totalStates 63 (cachedPairCap 4 4 3)) := blockCfg memory
      (⟨cachedPairPort 4 4 3,bankNative x y m later (freshGap x y) (leftMagnitude x y) (rightMagnitude x y)⟩ :
        MachineState (cachedPairCap 4 4 3))
    have start : first=blockCfg memory (⟨0,bankWork x y m later (freshGap x y)⟩ : MachineState (cachedPairCap 4 4 3)) :=
      row_entry_cfg (cachedPairCap 4 4 3) (cachedPairMachine 63 4 4 3) memory
        (bankWork x y m later (freshGap x y))
    have actual : PSTRTMSeq005.RunsFrom (component (2 : Fin 19)).code first tr last :=
      ⟨run.1.trans (congrArg some start.symm),run.2.1,run.2.2.1,run.2.2.2⟩
    have decoded : (component (2 : Fin 19)).decode last.q=widen64 memory :=
      row64_decode (cachedPairCap 4 4 3) (cachedPairMachine 63 4 4 3) memory (cachedPairPort 4 4 3)
    have step := transfer_to mode (2 : Fin 19) 4 (by decide) last (widen64 memory) (widen64 memory)
      last.Tape actual.2.2.2 decoded rfl rfl rfl
    have segment := component_segment mode (2 : Fin 19) _ _ _ actual
    refine ⟨liftTrace (2 : Fin 19) tr,liftCfg (2 : Fin 19) last,segment,step,?_⟩
    exact (liftTrace_length (2 : Fin 19) tr).trans_le len

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubChoice076
