module
public import Structure.PA17_TM_RatArithmetic_MulController_057c

/-! Actual local-run lifting, charged write-self transitions, final HALT and original zero-label initialization. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulController057

open Turing PA17TMDivisionCompose006
open scoped BigOperators
attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticFirstRaw052.firstCap PA17TMRatArithmeticFirstRaw052.bridgeCap
  PA17TMRatArithmeticFirstRaw052.commonCap PA17TMRatArithmeticFirstMul051.cycleCap
  PA17TMRatArithmeticCachedOuter043.carryCap PA17TMRatArithmeticNativeTail055.carriedTailCap
  PA17TMRatArithmeticZeroCarry058.observeCap PA17TMRatArithmeticSignDispatch053.dispatchCap

attribute [local implicit_reducible] controllerCap

/-- Local execution lifts with the SAME trace; component HALT has not
been identified with global HALT or a free transition. -/
theorem component_segment (phase : Fin 17) (first last : MachineState (component phase).states)
    (trace : List (MachineState (component phase).states))
    (run : PSTRTMSeq005.RunsFrom (component phase).code first trace last) :
    Segment mulMachine (liftCfg phase first) (liftTrace phase trace) (liftCfg phase last) := by
  have padded := pad_runsFrom (component_fits phase) (component phase).code first last trace run
  have lifted : Segment (states:=controllerCap) mulMachine (liftCfg phase first)
      ((trace.map (padCfg (component_fits phase))).map (blockCfg (p:=16) (s:=commonCap) phase))
      (liftCfg phase last) :=
    block_segment (p:=16) (s:=commonCap) controllerFamily controllerPorts phase _ _ _ padded
  have maps : (trace.map (padCfg (component_fits phase))).map (blockCfg (p:=16) (s:=commonCap) phase)=
      liftTrace phase trace := by
    rw [List.map_map]
    rfl
  rw [maps] at lifted
  exact lifted

/-- One actual write-self transition, retaining the entire physical tape
and head. The next finite row is decoded from the actual local HALT. -/
theorem paid_transfer (phase : Fin 17) (h : phase.val<16)
    (last : MachineState (component phase).states)
    (halt : TM0.step (component phase).code last=none) :
    TM0.step mulMachine (liftCfg phase last)=
      some (entryCfg (nextPhase phase) ((component phase).decode last.q) last.Tape) := by
  have paddedHalt : TM0.step (controllerFamily phase) (padCfg (component_fits phase) last)=none := by
    simp only [controllerFamily,pad_step,halt,Option.map_none]
  have port : controllerPorts phase (padCfg (component_fits phase) last).q=
      some (nextPhase phase,padLabel (component_fits (nextPhase phase))
        ((component (nextPhase phase)).entry ((component phase).decode last.q))) := by
    simp only [controllerPorts,ite_eq_left h,padCfg,localCode_pad]
  change TM0.step (blockMachine (p:=16) (s:=commonCap) controllerFamily controllerPorts)
      (blockCfg (p:=16) (s:=commonCap) phase (padCfg (component_fits phase) last))=
    some (blockCfg (p:=16) (s:=commonCap) (nextPhase phase)
      (⟨padLabel (component_fits (nextPhase phase))
        ((component (nextPhase phase)).entry ((component phase).decode last.q)),last.Tape⟩ : MachineState commonCap))
  exact block_transfer (p:=16) (s:=commonCap) controllerFamily controllerPorts phase
    (padCfg (component_fits phase) last)
    (nextPhase phase,padLabel (component_fits (nextPhase phase))
      ((component (nextPhase phase)).entry ((component phase).decode last.q))) paddedHalt port

theorem final_halt (last : MachineState (component (16 : Fin 17)).states)
    (halt : TM0.step (component (16 : Fin 17)).code last=none) :
    TM0.step mulMachine (liftCfg (16 : Fin 17) last)=none := by
  have paddedHalt : TM0.step (controllerFamily (16 : Fin 17))
      (padCfg (component_fits (16 : Fin 17)) last)=none := by
    simp only [controllerFamily,pad_step,halt,Option.map_none]
  exact block_halt controllerFamily controllerPorts (16 : Fin 17) _ paddedHalt rfl

theorem final_runs (first last : MachineState (component (16 : Fin 17)).states)
    (trace : List (MachineState (component (16 : Fin 17)).states))
    (run : PSTRTMSeq005.RunsFrom (component (16 : Fin 17)).code first trace last) :
    PSTRTMSeq005.RunsFrom mulMachine (liftCfg (16 : Fin 17) first)
      (liftTrace (16 : Fin 17) trace) (liftCfg (16 : Fin 17) last) :=
  segment_runsFrom _ _ _ _ (component_segment (16 : Fin 17) first last trace run)
    (final_halt last run.2.2.2)

theorem initial_zero (memory : Fin 128) (tape : Tape Bool) :
    entryCfg (0 : Fin 17) memory tape=(⟨0,tape⟩ : MachineState controllerCap) := by
  change blockCfg (0 : Fin 17) (padCfg (component_fits (0 : Fin 17))
    (⟨0,tape⟩ : MachineState (component (0 : Fin 17)).states))=_
  rw [PA17TMRatArithmeticBookmark014.pad_zero,blockCfg_zero]

theorem initial_mapped (input : List Bool) :
    liftCfg (0 : Fin 17)
      (TM0.init input : MachineState (component (0 : Fin 17)).states)=
      (TM0.init input : MachineState controllerCap) := by
  change blockCfg (0 : Fin 17) (padCfg (component_fits (0 : Fin 17))
    (⟨0,Tape.mk₁ input⟩ : MachineState (component (0 : Fin 17)).states))=
      (⟨0,Tape.mk₁ input⟩ : MachineState controllerCap)
  rw [PA17TMRatArithmeticBookmark014.pad_zero,blockCfg_zero]

/-- Both physically observed B exits retain all seven carry bits. The
subsequent paid_transfer, rather than a host relabel, enters shared053. -/
theorem ready_decode (memory : Fin 128) (bitB : Bool) :
    ready128.decode (label memory (PA17TMRatArithmeticCachedPair054.cachedReadyPort 4 1 0 bitB))=memory :=
  row128_decode _ _ memory _

theorem allocation64_decode (total : Nat) (memory : Fin 64) (tape : Tape Bool) :
    (allocation64 total).decode
      (PA17TMRatArithmeticCachedOuter043.carryFinal 63 total PA17TMRatArithmeticWideCache045.allocationK memory tape).q=
      widen64 memory := row64_decode _ _ memory _

theorem allocation128_decode (total : Nat) (memory : Fin 128) (tape : Tape Bool) :
    (allocation128 total).decode
      (PA17TMRatArithmeticCachedOuter043.carryFinal 127 total PA17TMRatArithmeticWideCache045.allocationK memory tape).q=
      memory := row128_decode _ _ memory _

theorem denominator_decode (memory : Fin 64) :
    denominators.decode (label memory (PA17TMRatArithmeticCachedPair054.originalPairPort 0))=widen64 memory :=
  row64_decode _ _ memory _

theorem cached_decode (later aLater bLater : Nat) (memory : Fin 64) :
    (cached64 later aLater bLater).decode
      (label memory (PA17TMRatArithmeticCachedPair054.cachedPairPort later aLater bLater))=widen64 memory :=
  row64_decode _ _ memory _

theorem tail_decode {states : Nat} (native : Machine states) (later : Nat) (memory : Fin 64) :
    (tail64 native later).decode (PA17TMRatArithmeticNativeTail055.carriedTailPort 63 states later memory)=widen64 memory :=
  row64_decode _ _ memory _


end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulController057
