module
public import Structure.PA17_TM_RatArithmetic_FirstRaw_052b
public import Structure.PA17_TM_RatArithmetic_FirstMul_051b
public import Structure.PA17_TM_RatArithmetic_MulController_057b
public import Structure.PA17_TM_RatArithmetic_MulClosure_059b
public import Structure.PA17_TM_RatArithmetic_CachedOuter_043e
public import Structure.PA17_TM_RatArithmetic_ZeroCarry_058e

/-! Fixed physical division prefix: raw parse/SX/allocation, Nx*Dy,
one real allocation, Dx*Ny, and actual D-zero observation/home return.
No branch on D-zero, GCD, quotient, or output program is installed here. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticDivPrefix067

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticMulController057 (Component row64Component row64_decode row64_entry widen64 narrow64)
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticFirstMul051 PA17TMRatArithmeticMulStart049
open PA17TMRatArithmeticMulClosure059 (bankHeader bankNative bankWork)
open scoped BigOperators
attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticFirstRaw052.bridgeCap PA17TMRatArithmeticFirstRaw052.commonCap
  PA17TMRatArithmeticFirstRaw052.firstCap cycleCap
  PA17TMRatArithmeticCachedOuter043.carryCap PA17TMRatArithmeticZeroCarry058.observeCap

/-- Pure capacities are fixed before any component containing code. -/
def firstStates : Nat := PA17TMRatArithmeticFirstRaw052.bridgeCap allocationK (cycleCap 63)
def allocationStates : Nat := PA17TMRatArithmeticCachedOuter043.carryCap 63 1 allocationK
def pairStates : Nat := totalStates 63 (PA17TMRatArithmeticCachedPair054.originalPairCap 0)
def recordStates : Nat := totalStates 63 1016
def observerStates : Nat := PA17TMRatArithmeticZeroCarry058.observeCap 0 1
attribute [local implicit_reducible] firstStates allocationStates pairStates recordStates observerStates

def componentStates (phase : Fin 5) : Nat :=
  match phase.val with
  | 0 => firstStates
  | 1 => allocationStates
  | 2 => pairStates
  | 3 => recordStates
  | _ => observerStates

def commonStates : Nat := ∑ phase : Fin 5, componentStates phase
def prefixCap : Nat := totalStates 4 commonStates
attribute [local implicit_reducible] prefixCap

def firstMachine : Machine firstStates :=
  PA17TMRatArithmeticFirstRaw052.bridgeMachine allocationK
    (cycleMachine 63 .nx .dy) (cycleEntry 63)

def firstComponent : Component :=
  ⟨firstStates,firstMachine,fun _ => 0,PA17TMRatArithmeticMulController057.firstDecode⟩

def pairComponent : Component :=
  row64Component (PA17TMRatArithmeticCachedPair054.originalPairCap 0)
    (PA17TMRatArithmeticCachedPair054.originalPairMachine 63 .dx .ny 0)

def recordFamily (_memory : Fin 64) : Machine 1016 := PA17TMRatArithmeticNativeCache030.mulCacheMachine
def recordPorts (_memory : Fin 64) (_q : Fin 1017) : Option (Fin 64 × Fin 1017) := none
def recordMachine : Machine recordStates := blockMachine recordFamily recordPorts
def recordComponent : Component := row64Component 1016 recordMachine

/-- The local native record HALT is arbitrary; only its actual outer row
is decoded. There is no returnHome before the D sensor. -/
theorem record_runs (memory : Fin 64) (first last : MachineState 1016)
    (trace : List (MachineState 1016))
    (run : PSTRTMSeq005.RunsFrom PA17TMRatArithmeticNativeCache030.mulCacheMachine first trace last) :
    PSTRTMSeq005.RunsFrom recordMachine (blockCfg memory first)
      (trace.map (blockCfg (s:=1016) memory)) (blockCfg memory last) :=
  block_runsFrom recordFamily recordPorts memory first last trace run rfl

theorem record_decode (memory : Fin 64) (actualLocal : Fin 1017) :
    recordComponent.decode (label memory actualLocal)=widen64 memory :=
  row64_decode 1016 recordMachine memory actualLocal

def observerMemory (q : Fin (observerStates+1)) : Fin 128 :=
  ⟨((phaseOf (p:=191) (s:=PA17TMRatArithmeticZeroCarry058.commonCap 0 1) q).val-64)%128,
    Nat.mod_lt _ (by decide)⟩

def observerComponent : Component :=
  ⟨observerStates,PA17TMRatArithmeticZeroCarry058.observeMachine 0 1,
    fun memory => PA17TMRatArithmeticZeroCarry058.observeEntry 0 1 (narrow64 memory),observerMemory⟩

theorem observer_decode (memory : Fin 128) :
    observerMemory (PA17TMRatArithmeticZeroCarry058.observePort 0 1 memory)=memory := by
  apply Fin.ext
  change ((phaseOf (label (PA17TMRatArithmeticZeroCarry058.newPhase memory)
    (padLabel (PA17TMRatArithmeticZeroCarry058.returnFits 0 1)
      (PA17TMRatArithmeticZeroCarry058.returnPort 0 1)))).val-64)%128=memory.val
  rw [phaseOf_label]
  change (64+memory.val-64)%128=memory.val
  rw [Nat.add_sub_cancel_left,Nat.mod_eq_of_lt memory.isLt]

def component (phase : Fin 5) : Component :=
  match phase.val with
  | 0 => firstComponent
  | 1 => PA17TMRatArithmeticMulController057.allocation64 1
  | 2 => pairComponent
  | 3 => recordComponent
  | _ => observerComponent

theorem component_states (phase : Fin 5) : (component phase).states=componentStates phase := by
  fin_cases phase <;> rfl

theorem component_fits (phase : Fin 5) : (component phase).states ≤ commonStates := by
  rw [component_states]
  exact Finset.single_le_sum (fun other _ => Nat.zero_le (componentStates other)) (Finset.mem_univ phase)

def family (phase : Fin 5) : Machine commonStates := padMachine (component_fits phase) (component phase).code
def nextPhase (phase : Fin 5) : Fin 5 := ⟨(phase.val+1)%5,Nat.mod_lt _ (by decide)⟩
def localCode (phase : Fin 5) (q : Fin (commonStates+1)) : Fin ((component phase).states+1) :=
  PA17TMRatArithmeticFirstRaw052.checkedIndex (component phase).states commonStates q

def ports (phase : Fin 5) (q : Fin (commonStates+1)) : Option (Fin 5 × Fin (commonStates+1)) :=
  if phase.val<4 then some (nextPhase phase,padLabel (component_fits (nextPhase phase))
    ((component (nextPhase phase)).entry ((component phase).decode (localCode phase q)))) else none

/-- ONE program, without original values, widths, gaps, answers or flags
as code parameters, before every original x,y. -/
def prefixMachine : Machine prefixCap := blockMachine family ports
def liftCfg (phase : Fin 5) (state : MachineState (component phase).states) : MachineState prefixCap :=
  blockCfg phase (padCfg (component_fits phase) state)
def entryCfg (phase : Fin 5) (memory : Fin 128) (tape : Tape Bool) : MachineState prefixCap :=
  liftCfg phase ⟨(component phase).entry memory,tape⟩
def liftTrace (phase : Fin 5) (trace : List (MachineState (component phase).states)) : List (MachineState prefixCap) :=
  trace.map (liftCfg phase)

theorem localCode_pad (phase : Fin 5) (q : Fin ((component phase).states+1)) :
    localCode phase (padLabel (component_fits phase) q)=q :=
  PA17TMRatArithmeticFirstRaw052.checkedIndex_pad (component_fits phase) q

theorem liftTrace_length (phase : Fin 5) (trace : List (MachineState (component phase).states)) :
    (liftTrace phase trace).length=trace.length := List.length_map _

theorem component_segment (phase : Fin 5) (first last : MachineState (component phase).states)
    (trace : List (MachineState (component phase).states))
    (run : PSTRTMSeq005.RunsFrom (component phase).code first trace last) :
    Segment prefixMachine (liftCfg phase first) (liftTrace phase trace) (liftCfg phase last) := by
  have padded := pad_runsFrom (component_fits phase) (component phase).code first last trace run
  have lifted : Segment (states:=prefixCap) prefixMachine (liftCfg phase first)
      ((trace.map (padCfg (component_fits phase))).map (blockCfg (p:=4) (s:=commonStates) phase))
      (liftCfg phase last) := block_segment (p:=4) (s:=commonStates) family ports phase _ _ _ padded
  have maps : (trace.map (padCfg (component_fits phase))).map (blockCfg (p:=4) (s:=commonStates) phase)=
      liftTrace phase trace := by
    rw [List.map_map]
    rfl
  rw [maps] at lifted
  exact lifted

theorem paid_transfer (phase : Fin 5) (h : phase.val<4) (last : MachineState (component phase).states)
    (halt : TM0.step (component phase).code last=none) :
    TM0.step prefixMachine (liftCfg phase last)=
      some (entryCfg (nextPhase phase) ((component phase).decode last.q) last.Tape) := by
  have halted : TM0.step (family phase) (padCfg (component_fits phase) last)=none := by
    simp only [family,pad_step,halt,Option.map_none]
  have port : ports phase (padCfg (component_fits phase) last).q=
      some (nextPhase phase,padLabel (component_fits (nextPhase phase))
        ((component (nextPhase phase)).entry ((component phase).decode last.q))) := by
    simp only [ports,ite_eq_left h,padCfg,localCode_pad]
  change TM0.step (blockMachine (p:=4) (s:=commonStates) family ports)
      (blockCfg (p:=4) (s:=commonStates) phase (padCfg (component_fits phase) last))=
    some (blockCfg (p:=4) (s:=commonStates) (nextPhase phase)
      (⟨padLabel (component_fits (nextPhase phase))
        ((component (nextPhase phase)).entry ((component phase).decode last.q)),last.Tape⟩ : MachineState commonStates))
  exact block_transfer (p:=4) (s:=commonStates) family ports phase (padCfg (component_fits phase) last)
    (nextPhase phase,padLabel (component_fits (nextPhase phase))
      ((component (nextPhase phase)).entry ((component phase).decode last.q))) halted port

theorem final_halt (last : MachineState (component (4 : Fin 5)).states)
    (halt : TM0.step (component (4 : Fin 5)).code last=none) :
    TM0.step prefixMachine (liftCfg (4 : Fin 5) last)=none := by
  have halted : TM0.step (family (4 : Fin 5)) (padCfg (component_fits (4 : Fin 5)) last)=none := by
    simp only [family,pad_step,halt,Option.map_none]
  exact block_halt (p:=4) (s:=commonStates) family ports (4 : Fin 5) _ halted rfl

theorem initial_mapped (input : List Bool) :
    liftCfg (0 : Fin 5) (TM0.init input : MachineState (component (0 : Fin 5)).states)=
      (TM0.init input : MachineState prefixCap) := by
  change blockCfg (0 : Fin 5) (padCfg (component_fits (0 : Fin 5))
    (⟨0,Tape.mk₁ input⟩ : MachineState (component (0 : Fin 5)).states))=
      (⟨0,Tape.mk₁ input⟩ : MachineState prefixCap)
  rw [PA17TMRatArithmeticBookmark014.pad_zero,blockCfg_zero]

theorem observer_fits : observerStates ≤ commonStates := component_fits (4 : Fin 5)

def prefixPort (memory : Fin 128) : Fin (prefixCap+1) :=
  label (4 : Fin 5) (padLabel observer_fits
    (PA17TMRatArithmeticZeroCarry058.observePort 0 1 memory))

def prefixMemory (q : Fin (prefixCap+1)) : Fin 128 :=
  observerMemory (PA17TMRatArithmeticFirstRaw052.checkedIndex observerStates commonStates
    (localOf (p:=4) (s:=commonStates) q))

theorem prefixPort_decode (memory : Fin 128) : prefixMemory (prefixPort memory)=memory := by
  unfold prefixMemory prefixPort
  rw [localOf_label,PA17TMRatArithmeticFirstRaw052.checkedIndex_pad observer_fits]
  exact observer_decode memory

def prefixComponent : Component := ⟨prefixCap,prefixMachine,fun _ => 0,prefixMemory⟩

/-- The original parsed bank and its counter/header are unchanged. These
are semantic names for actual stored canonical cache tapes, not inputs. -/
def postTape (x y : Rat) (gapM gapD : Nat) : Tape Bool :=
  bankHeader x y [resultRecord gapM (x.num.natAbs*y.den),resultRecord gapD (x.den*y.num.natAbs)]

def observed (x y : Rat) : Fin 128 :=
  PA17TMRatArithmeticZeroCarry058.observedMemory (actualMemory x y) (decide (x.den*y.num.natAbs=0))

def prefixFinal (x y : Rat) (gapM gapD : Nat) : MachineState prefixCap :=
  ⟨prefixPort (observed x y),postTape x y gapM gapD⟩

theorem prefixFinal_decode (x y : Rat) (gapM gapD : Nat) :
    prefixMemory (prefixFinal x y gapM gapD).q=observed x y := prefixPort_decode _

theorem prefixFinal_old_memory (x y : Rat) (gapM gapD : Nat) :
    (prefixMemory (prefixFinal x y gapM gapD).q).val%64=(actualMemory x y).val := by
  rw [prefixFinal_decode]
  exact PA17TMRatArithmeticZeroCarry058.observedMemory_retains_old _ _

theorem prefixFinal_zero_bit (x y : Rat) (gapM gapD : Nat) :
    (prefixMemory (prefixFinal x y gapM gapD).q).val/64=
      if decide (x.den*y.num.natAbs=0) then 1 else 0 := by
  rw [prefixFinal_decode]
  exact PA17TMRatArithmeticZeroCarry058.observedMemory_zero_bit _ _

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticDivPrefix067
