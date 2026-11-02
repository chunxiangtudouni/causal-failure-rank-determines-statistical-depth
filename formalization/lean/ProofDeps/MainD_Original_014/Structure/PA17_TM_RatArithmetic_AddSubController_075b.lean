module
public import Structure.PA17_TM_RatArithmetic_AddSubController_075a

/-! Lifting of the same real local traces, actual branch/remap write-self
transitions, true final HALT and the original zero-label initialization. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubController075

open Turing PA17TMDivisionCompose006
attribute [local implicit_reducible] totalStates controllerCap

theorem component_segment (subtract : Bool) (phase : Fin 19)
    (first last : MachineState (component phase).states)
    (trace : List (MachineState (component phase).states))
    (run : PSTRTMSeq005.RunsFrom (component phase).code first trace last) :
    Segment (addSubMachine subtract) (liftCfg phase first) (liftTrace phase trace) (liftCfg phase last) := by
  have padded := pad_runsFrom (component_fits phase) (component phase).code first last trace run
  have lifted : Segment (states:=controllerCap) (addSubMachine subtract) (liftCfg phase first)
      ((trace.map (padCfg (component_fits phase))).map (blockCfg (p:=18) (s:=commonCap) phase))
      (liftCfg phase last) :=
    block_segment (p:=18) (s:=commonCap) family (ports subtract) phase _ _ _ padded
  have maps : (trace.map (padCfg (component_fits phase))).map (blockCfg (p:=18) (s:=commonCap) phase)=
      liftTrace phase trace := by rw [List.map_map];rfl
  rw [maps] at lifted
  exact lifted

/-- A true local HALT causes one paid transition. The target row uses
only the physically retained row and, at phase5, the actual P-zero bit. -/
theorem paid_transfer (subtract : Bool) (phase : Fin 19) (h : phase.val<18)
    (last : MachineState (component phase).states)
    (halt : TM0.step (component phase).code last=none) :
    TM0.step (addSubMachine subtract) (liftCfg phase last)=
      some (entryCfg (nextPhase subtract phase ((component phase).decode last.q))
        (nextMemory subtract phase ((component phase).decode last.q)) last.Tape) := by
  have paddedHalt : TM0.step (family phase) (padCfg (component_fits phase) last)=none := by
    simp only [family,pad_step,halt,Option.map_none]
  let choose : Fin 128 → Option (Fin 19 × Fin (commonCap+1)) := fun memory =>
    some (nextPhase subtract phase memory,padLabel (component_fits (nextPhase subtract phase memory))
      ((component (nextPhase subtract phase memory)).entry (nextMemory subtract phase memory)))
  have decoded : (component phase).decode (localCode phase (padLabel (component_fits phase) last.q))=
      (component phase).decode last.q :=
    congrArg ((component phase).decode) (localCode_pad phase last.q)
  have port : ports subtract phase (padCfg (component_fits phase) last).q=
      some (nextPhase subtract phase ((component phase).decode last.q),
        padLabel (component_fits (nextPhase subtract phase ((component phase).decode last.q)))
          ((component (nextPhase subtract phase ((component phase).decode last.q))).entry
            (nextMemory subtract phase ((component phase).decode last.q)))) := by
    change (if phase.val<18 then choose ((component phase).decode
      (localCode phase (padLabel (component_fits phase) last.q))) else none)=
      choose ((component phase).decode last.q)
    rw [ite_eq_left h]
    exact congrArg choose decoded
  change TM0.step (blockMachine (p:=18) (s:=commonCap) family (ports subtract))
      (blockCfg (p:=18) (s:=commonCap) phase (padCfg (component_fits phase) last))=
    some (blockCfg (p:=18) (s:=commonCap)
      (nextPhase subtract phase ((component phase).decode last.q))
      (⟨padLabel (component_fits (nextPhase subtract phase ((component phase).decode last.q)))
        ((component (nextPhase subtract phase ((component phase).decode last.q))).entry
          (nextMemory subtract phase ((component phase).decode last.q))),last.Tape⟩ : MachineState commonCap))
  exact block_transfer (p:=18) (s:=commonCap) family (ports subtract) phase
    (padCfg (component_fits phase) last)
    (nextPhase subtract phase ((component phase).decode last.q),
      padLabel (component_fits (nextPhase subtract phase ((component phase).decode last.q)))
        ((component (nextPhase subtract phase ((component phase).decode last.q))).entry
          (nextMemory subtract phase ((component phase).decode last.q)))) paddedHalt port

theorem transfer_to (subtract : Bool) (phase target : Fin 19) (h : phase.val<18)
    (last : MachineState (component phase).states) (memory outputMemory : Fin 128) (tape : Tape Bool)
    (halt : TM0.step (component phase).code last=none)
    (decoded : (component phase).decode last.q=memory)
    (branch : nextPhase subtract phase memory=target)
    (remap : nextMemory subtract phase memory=outputMemory) (whole : last.Tape=tape) :
    TM0.step (addSubMachine subtract) (liftCfg phase last)=some (entryCfg target outputMemory tape) := by
  rw [paid_transfer subtract phase h last halt,decoded,branch,remap,whole]

theorem final_halt (subtract : Bool) (last : MachineState (component (18 : Fin 19)).states)
    (halt : TM0.step (component (18 : Fin 19)).code last=none) :
    TM0.step (addSubMachine subtract) (liftCfg (18 : Fin 19) last)=none := by
  have paddedHalt : TM0.step (family (18 : Fin 19))
      (padCfg (component_fits (18 : Fin 19)) last)=none := by
    simp only [family,pad_step,halt,Option.map_none]
  exact block_halt family (ports subtract) (18 : Fin 19) _ paddedHalt rfl

theorem final_runs (subtract : Bool)
    (first last : MachineState (component (18 : Fin 19)).states)
    (trace : List (MachineState (component (18 : Fin 19)).states))
    (run : PSTRTMSeq005.RunsFrom (component (18 : Fin 19)).code first trace last) :
    PSTRTMSeq005.RunsFrom (addSubMachine subtract) (liftCfg (18 : Fin 19) first)
      (liftTrace (18 : Fin 19) trace) (liftCfg (18 : Fin 19) last) :=
  segment_runsFrom _ _ _ _ (component_segment subtract (18 : Fin 19) first last trace run)
    (final_halt subtract last run.2.2.2)

theorem initial_zero (memory : Fin 128) (tape : Tape Bool) :
    entryCfg (0 : Fin 19) memory tape=(⟨0,tape⟩ : MachineState controllerCap) := by
  change blockCfg (0 : Fin 19) (padCfg (component_fits (0 : Fin 19))
    (⟨0,tape⟩ : MachineState (component (0 : Fin 19)).states))=_
  rw [PA17TMRatArithmeticBookmark014.pad_zero,blockCfg_zero]

theorem initial_mapped (input : List Bool) :
    liftCfg (0 : Fin 19) (TM0.init input : MachineState (component (0 : Fin 19)).states)=
      (TM0.init input : MachineState controllerCap) := by
  change blockCfg (0 : Fin 19) (padCfg (component_fits (0 : Fin 19))
    (⟨0,Tape.mk₁ input⟩ : MachineState (component (0 : Fin 19)).states))=
      (⟨0,Tape.mk₁ input⟩ : MachineState controllerCap)
  rw [PA17TMRatArithmeticBookmark014.pad_zero,blockCfg_zero]

theorem linear_next (subtract : Bool) (phase : Fin 19) (memory : Fin 128)
    (h1 : phase.val≠1) (h2 : phase.val≠2) :
    nextPhase subtract phase memory=⟨(phase.val+1)%19,Nat.mod_lt _ (by decide)⟩ := by
  simp only [nextPhase,ite_eq_right h1,ite_eq_right h2]

theorem unchanged_memory (subtract : Bool) (phase : Fin 19) (memory : Fin 128) (h : phase.val≠5) :
    nextMemory subtract phase memory=memory := ite_eq_right h

theorem selected_pair_phase (subtract : Bool) (memory : Fin 64) :
    nextPhase subtract (1 : Fin 19) (PA17TMRatArithmeticMulController057.widen64 memory)=
      if sameSignsFromMemory subtract memory then (2 : Fin 19) else 3 := by
  change (if sameSignsFromMemory subtract
    (PA17TMRatArithmeticMulController057.narrow64
      (PA17TMRatArithmeticMulController057.widen64 memory)) then (2 : Fin 19) else 3)=_
  rw [PA17TMRatArithmeticMulController057.narrow_widen]

theorem observed_sign_transfer (subtract : Bool) (memory : Fin 64) (pZero : Bool) :
    nextMemory subtract (5 : Fin 19) (PA17TMRatArithmeticZeroCarry058.observedMemory memory pZero)=
      PA17TMRatArithmeticMulController057.widen64
        (PA17TMRatArithmeticSignedSumFields072.selectedMemory subtract memory pZero) := by
  change repairedMemory subtract (PA17TMRatArithmeticZeroCarry058.observedMemory memory pZero)=_
  exact repaired_observed subtract memory pZero

/- Pure descriptors of values genuinely produced by the local programs.
None of these descriptors is an argument of addSubMachine. -/
open PA17TMRatArithmeticSignedSumFields072 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticNativeSize007 PA17TMRatArithmeticParse002

def originalPower (x y : Rat) : Nat := ((encode [.rational x,.rational y]).length+1)^4
def mRecord (x y : Rat) (gap : Nat) := resultRecord gap (leftMagnitude x y)
def nRecord (x y : Rat) (gap : Nat) := resultRecord gap (rightMagnitude x y)
def eRecord (x y : Rat) (gap : Nat) := resultRecord gap (commonDenominator x y)
def pRecord (x y : Rat) (gap : Nat) := resultRecord gap (leftDifference x y)
def qRecord (x y : Rat) (gap : Nat) := resultRecord gap (rightDifference x y)
def rRecord (subtract : Bool) (x y : Rat) (gap : Nat) := resultRecord gap (sumMagnitude subtract x y)
def gRecord (subtract : Bool) (x y : Rat) (gap : Nat) := resultRecord gap (normalizer subtract x y)
def uRecord (subtract : Bool) (x y : Rat) (gap : Nat) := resultRecord gap (quotientNumerator subtract x y)
def vRecord (subtract : Bool) (x y : Rat) (gap : Nat) := resultRecord gap (quotientDenominator subtract x y)

def resultMemory (subtract : Bool) (x y : Rat) : Fin 64 :=
  selectedMemory subtract (PA17TMRatArithmeticMulStart049.actualMemory x y) (decide (leftDifference x y=0))
def finalMemory (subtract : Bool) (x y : Rat) : Fin 128 :=
  PA17TMRatArithmeticZeroCarry058.observedMemory (resultMemory subtract x y)
    (decide (quotientNumerator subtract x y=0))

theorem final_output_sign (subtract : Bool) (x y : Rat) :
    PA17TMRatArithmeticZeroCarry058.repairedNegative (finalMemory subtract x y)=sign (target subtract x y) :=
  observed_output_sign subtract x y

theorem result_record_width (x y : Rat) (value gap : Nat) (h : natBits value≤fieldWidth x y) :
    (resultRecord gap value).digits.length≤fieldWidth x y := by
  simpa only [resultRecord,PSTRTMNatValue017.rawPayload,List.length_ofFn] using h

theorem record_widths (subtract : Bool) (x y : Rat) (gm gn ge gp gq gr gg gu gv : Nat) :
    (mRecord x y gm).digits.length≤fieldWidth x y ∧ (nRecord x y gn).digits.length≤fieldWidth x y ∧
    (eRecord x y ge).digits.length≤fieldWidth x y ∧ (pRecord x y gp).digits.length≤fieldWidth x y ∧
    (qRecord x y gq).digits.length≤fieldWidth x y ∧ (rRecord subtract x y gr).digits.length≤fieldWidth x y ∧
    (gRecord subtract x y gg).digits.length≤fieldWidth x y ∧ (uRecord subtract x y gu).digits.length≤fieldWidth x y ∧
    (vRecord subtract x y gv).digits.length≤fieldWidth x y := by
  obtain ⟨hm,hn,he,hp,hq,hr,hg,hu,hv⟩ := all_field_bits subtract x y
  exact ⟨result_record_width x y _ _ hm,result_record_width x y _ _ hn,
    result_record_width x y _ _ he,result_record_width x y _ _ hp,result_record_width x y _ _ hq,
    result_record_width x y _ _ hr,result_record_width x y _ _ hg,result_record_width x y _ _ hu,
    result_record_width x y _ _ hv⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubController075
