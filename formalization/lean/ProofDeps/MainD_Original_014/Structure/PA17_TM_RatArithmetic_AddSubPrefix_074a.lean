module
public import Structure.PA17_TM_RatArithmetic_DivPrefix_067b
public import Structure.PA17_TM_RatArithmetic_SignedSumFields_072a
public import Structure.PA17_TM_RatArithmetic_PairBounds_061a

/-! One fixed raw two-Rat prefix producing M,N,E,P,Q. All native calls,
allocations, copies and returns are physical; each component transition
is an actual write-self. No arithmetic mode or input value selects code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubPrefix074

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticMulController057 (Component row64Component row64_decode widen64 narrow64)
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticNativeTail055
open PA17TMRatArithmeticMulStart049 PA17TMRatArithmeticSignedSumFields072
open PA17TMRatArithmeticMulClosure059 (bankHeader bankNative bankWork)
open scoped BigOperators
attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticCachedOuter043.carryCap carriedTailCap tailCap nativeRecordCap
  PA17TMRatArithmeticCachedPair054.originalPairCap PA17TMRatArithmeticCachedPair054.cachedPairCap

/-- These Nat capacities do not project any machine-containing record. -/
def firstStates : Nat := PA17TMRatArithmeticDivPrefix067.prefixCap
def allocationStates (total : Nat) : Nat := PA17TMRatArithmeticCachedOuter043.carryCap 63 total allocationK
def originalStates : Nat := totalStates 63 (PA17TMRatArithmeticCachedPair054.originalPairCap 1)
def mulStates : Nat := carriedTailCap 63 982 1
def leftPairStates : Nat := totalStates 63 (PA17TMRatArithmeticCachedPair054.cachedPairCap 2 2 1)
def leftStates : Nat := carriedTailCap 63 596 2
def rightPairStates : Nat := totalStates 63 (PA17TMRatArithmeticCachedPair054.cachedPairCap 3 2 3)
def rightStates : Nat := carriedTailCap 63 596 3
attribute [local implicit_reducible] firstStates allocationStates originalStates mulStates
  leftPairStates leftStates rightPairStates rightStates

def componentStates (phase : Fin 10) : Nat :=
  match phase.val with
  | 0 => firstStates
  | 1 => allocationStates 2
  | 2 => originalStates
  | 3 => mulStates
  | 4 => allocationStates 3
  | 5 => leftPairStates
  | 6 => leftStates
  | 7 => allocationStates 4
  | 8 => rightPairStates
  | _ => rightStates

def commonStates : Nat := ∑ phase : Fin 10, componentStates phase
def prefixCap : Nat := totalStates 9 commonStates
attribute [local implicit_reducible] prefixCap

def originalComponent : Component :=
  row64Component (PA17TMRatArithmeticCachedPair054.originalPairCap 1)
    (PA17TMRatArithmeticCachedPair054.originalPairMachine 63 .dx .dy 1)

def component (phase : Fin 10) : Component :=
  match phase.val with
  | 0 => PA17TMRatArithmeticDivPrefix067.prefixComponent
  | 1 => PA17TMRatArithmeticMulController057.allocation64 2
  | 2 => originalComponent
  | 3 => PA17TMRatArithmeticMulController057.tail64 PSTRTMNativeMul112.nativeMulMachine 1
  | 4 => PA17TMRatArithmeticMulController057.allocation64 3
  | 5 => PA17TMRatArithmeticMulController057.cached64 2 2 1
  | 6 => PA17TMRatArithmeticMulController057.tail64 PA17TMRatArithmeticSub016.nativeSubMachine 2
  | 7 => PA17TMRatArithmeticMulController057.allocation64 4
  | 8 => PA17TMRatArithmeticMulController057.cached64 3 2 3
  | _ => PA17TMRatArithmeticMulController057.tail64 PA17TMRatArithmeticSub016.nativeSubMachine 3

theorem component_states (phase : Fin 10) : (component phase).states=componentStates phase := by
  fin_cases phase <;> rfl

theorem component_fits (phase : Fin 10) : (component phase).states ≤ commonStates := by
  rw [component_states]
  exact Finset.single_le_sum (fun other _ => Nat.zero_le (componentStates other)) (Finset.mem_univ phase)

def family (phase : Fin 10) : Machine commonStates := padMachine (component_fits phase) (component phase).code
def nextPhase (phase : Fin 10) : Fin 10 := ⟨(phase.val+1)%10,Nat.mod_lt _ (by decide)⟩
def localCode (phase : Fin 10) (q : Fin (commonStates+1)) : Fin ((component phase).states+1) :=
  PA17TMRatArithmeticFirstRaw052.checkedIndex (component phase).states commonStates q

def ports (phase : Fin 10) (q : Fin (commonStates+1)) : Option (Fin 10 × Fin (commonStates+1)) :=
  if phase.val<9 then some (nextPhase phase,padLabel (component_fits (nextPhase phase))
    ((component (nextPhase phase)).entry ((component phase).decode (localCode phase q)))) else none

/-- ONE program, without original values, widths, gaps, answers or flags
as code parameters, before every original x,y. -/
def prefixMachine : Machine prefixCap := blockMachine family ports
def liftCfg (phase : Fin 10) (state : MachineState (component phase).states) : MachineState prefixCap :=
  blockCfg phase (padCfg (component_fits phase) state)
def entryCfg (phase : Fin 10) (memory : Fin 128) (tape : Tape Bool) : MachineState prefixCap :=
  liftCfg phase ⟨(component phase).entry memory,tape⟩
def liftTrace (phase : Fin 10) (trace : List (MachineState (component phase).states)) : List (MachineState prefixCap) :=
  trace.map (liftCfg phase)

theorem localCode_pad (phase : Fin 10) (q : Fin ((component phase).states+1)) :
    localCode phase (padLabel (component_fits phase) q)=q :=
  PA17TMRatArithmeticFirstRaw052.checkedIndex_pad (component_fits phase) q

theorem liftTrace_length (phase : Fin 10) (trace : List (MachineState (component phase).states)) :
    (liftTrace phase trace).length=trace.length := List.length_map _

theorem component_segment (phase : Fin 10) (first last : MachineState (component phase).states)
    (trace : List (MachineState (component phase).states))
    (run : PSTRTMSeq005.RunsFrom (component phase).code first trace last) :
    Segment prefixMachine (liftCfg phase first) (liftTrace phase trace) (liftCfg phase last) := by
  have padded := pad_runsFrom (component_fits phase) (component phase).code first last trace run
  have lifted : Segment (states:=prefixCap) prefixMachine (liftCfg phase first)
      ((trace.map (padCfg (component_fits phase))).map (blockCfg (p:=9) (s:=commonStates) phase))
      (liftCfg phase last) := block_segment (p:=9) (s:=commonStates) family ports phase _ _ _ padded
  have maps : (trace.map (padCfg (component_fits phase))).map (blockCfg (p:=9) (s:=commonStates) phase)=
      liftTrace phase trace := by
    rw [List.map_map]
    rfl
  rw [maps] at lifted
  exact lifted

theorem paid_transfer (phase : Fin 10) (h : phase.val<9) (last : MachineState (component phase).states)
    (halt : TM0.step (component phase).code last=none) :
    TM0.step prefixMachine (liftCfg phase last)=
      some (entryCfg (nextPhase phase) ((component phase).decode last.q) last.Tape) := by
  have halted : TM0.step (family phase) (padCfg (component_fits phase) last)=none := by
    simp only [family,pad_step,halt,Option.map_none]
  have port : ports phase (padCfg (component_fits phase) last).q=
      some (nextPhase phase,padLabel (component_fits (nextPhase phase))
        ((component (nextPhase phase)).entry ((component phase).decode last.q))) := by
    simp only [ports,ite_eq_left h,padCfg,localCode_pad]
  change TM0.step (blockMachine (p:=9) (s:=commonStates) family ports)
      (blockCfg (p:=9) (s:=commonStates) phase (padCfg (component_fits phase) last))=
    some (blockCfg (p:=9) (s:=commonStates) (nextPhase phase)
      (⟨padLabel (component_fits (nextPhase phase))
        ((component (nextPhase phase)).entry ((component phase).decode last.q)),last.Tape⟩ : MachineState commonStates))
  exact block_transfer (p:=9) (s:=commonStates) family ports phase (padCfg (component_fits phase) last)
    (nextPhase phase,padLabel (component_fits (nextPhase phase))
      ((component (nextPhase phase)).entry ((component phase).decode last.q))) halted port

theorem final_halt (last : MachineState (component (9 : Fin 10)).states)
    (halt : TM0.step (component (9 : Fin 10)).code last=none) :
    TM0.step prefixMachine (liftCfg (9 : Fin 10) last)=none := by
  have halted : TM0.step (family (9 : Fin 10)) (padCfg (component_fits (9 : Fin 10)) last)=none := by
    simp only [family,pad_step,halt,Option.map_none]
  exact block_halt (p:=9) (s:=commonStates) family ports (9 : Fin 10) _ halted rfl

theorem initial_mapped (input : List Bool) :
    liftCfg (0 : Fin 10) (TM0.init input : MachineState (component (0 : Fin 10)).states)=
      (TM0.init input : MachineState prefixCap) := by
  change blockCfg (0 : Fin 10) (padCfg (component_fits (0 : Fin 10))
    (⟨0,Tape.mk₁ input⟩ : MachineState (component (0 : Fin 10)).states))=
      (⟨0,Tape.mk₁ input⟩ : MachineState prefixCap)
  rw [PA17TMRatArithmeticBookmark014.pad_zero,blockCfg_zero]

theorem final_fits : rightStates ≤ commonStates := component_fits (9 : Fin 10)

def prefixPort (memory : Fin 64) : Fin (prefixCap+1) :=
  label (9 : Fin 10) (padLabel final_fits (carriedTailPort 63 596 3 memory))

def prefixMemory (q : Fin (prefixCap+1)) : Fin 128 :=
  widen64 (phaseOf (p:=63) (s:=tailCap 596 3)
    (PA17TMRatArithmeticFirstRaw052.checkedIndex rightStates commonStates
      (localOf (p:=9) (s:=commonStates) q)))

theorem prefixPort_decode (memory : Fin 64) : prefixMemory (prefixPort memory)=widen64 memory := by
  unfold prefixMemory prefixPort
  rw [localOf_label,PA17TMRatArithmeticFirstRaw052.checkedIndex_pad final_fits]
  exact congrArg widen64 (phaseOf_label memory (tailPort 596 3))

def prefixComponent : Component := ⟨prefixCap,prefixMachine,fun _ => 0,prefixMemory⟩

def postTape (x y : Rat) (gm gn ge gp gq : Nat) : Tape Bool :=
  bankHeader x y [resultRecord gm (leftMagnitude x y),resultRecord gn (rightMagnitude x y),
    resultRecord ge (commonDenominator x y),resultRecord gp (leftDifference x y),
    resultRecord gq (rightDifference x y)]

def prefixFinal (x y : Rat) (gm gn ge gp gq : Nat) : MachineState prefixCap :=
  ⟨prefixPort (actualMemory x y),postTape x y gm gn ge gp gq⟩

theorem prefixFinal_decode (x y : Rat) (gm gn ge gp gq : Nat) :
    prefixMemory (prefixFinal x y gm gn ge gp gq).q=widen64 (actualMemory x y) := prefixPort_decode _

/-- This is only the interpretation of the actual incoming067 port. The
controller's paid phase0 transfer really installs the next narrow64 row. -/
theorem first_memory_narrow (x y : Rat) (gm gn : Nat) :
    narrow64 (PA17TMRatArithmeticDivPrefix067.prefixMemory
      (PA17TMRatArithmeticDivPrefix067.prefixFinal x y gm gn).q)=actualMemory x y := by
  apply Fin.ext
  exact PA17TMRatArithmeticDivPrefix067.prefixFinal_old_memory x y gm gn

/-- Opaque-state transports avoid rewriting a whole Segment containing
large finite-state indices and machine code. They preserve its trace. -/
theorem retarget_first {states : Nat} (code : Machine states)
    (first next last : MachineState states) (trace : List (MachineState states))
    (same : first=next) (run : Segment code first trace last) : Segment code next trace last := same ▸ run

theorem retarget_last {states : Nat} (code : Machine states)
    (first last next : MachineState states) (trace : List (MachineState states))
    (same : last=next) (run : Segment code first trace last) : Segment code first trace next := same ▸ run

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubPrefix074
