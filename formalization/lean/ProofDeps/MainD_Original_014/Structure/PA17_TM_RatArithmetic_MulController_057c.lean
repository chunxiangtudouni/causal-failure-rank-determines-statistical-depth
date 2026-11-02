module
public import Structure.PA17_TM_RatArithmetic_MulController_057b

/-! The same single fixed seventeen-phase controller, pure capacity table and physical configuration maps. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulController057

open Turing PA17TMDivisionCompose006
open scoped BigOperators
attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticFirstRaw052.firstCap PA17TMRatArithmeticFirstRaw052.bridgeCap
  PA17TMRatArithmeticFirstRaw052.commonCap PA17TMRatArithmeticFirstMul051.cycleCap
  PA17TMRatArithmeticCachedOuter043.carryCap PA17TMRatArithmeticNativeTail055.carriedTailCap
  PA17TMRatArithmeticZeroCarry058.observeCap PA17TMRatArithmeticSignDispatch053.dispatchCap

/-- Allocation uses TOTAL record counts 1..5. Pair/native/home/output
interfaces instead count LATER records after their mandatory first. -/
def component (phase : Fin 17) : Component :=
  match phase.val with
  | 0 => firstComponent
  | 1 => allocation64 1
  | 2 => denominators
  | 3 => tail64 PSTRTMNativeMul112.nativeMulMachine 0
  | 4 => allocation64 2
  | 5 => cached64 1 1 0
  | 6 => tail64 ROOTTMGCDDispatch018.nativeGcdMachine 1
  | 7 => allocation64 3
  | 8 => cached64 2 2 0
  | 9 => tail64 PA17TMDivisionFull012.quotientMachine 2
  | 10 => allocation64 4
  | 11 => cached64 3 2 1
  | 12 => quotientRecordComponent
  | 13 => zeroComponent
  | 14 => allocation128 5
  | 15 => ready128
  | _ => outputComponent

/-- A pure Nat table separated from all code-containing record projections. -/
def componentStates (phase : Fin 17) : Nat :=
  match phase.val with
  | 0 => PA17TMRatArithmeticFirstRaw052.firstCap
  | 1 => PA17TMRatArithmeticCachedOuter043.carryCap 63 1 PA17TMRatArithmeticWideCache045.allocationK
  | 2 => totalStates 63 (PA17TMRatArithmeticCachedPair054.originalPairCap 0)
  | 3 => PA17TMRatArithmeticNativeTail055.carriedTailCap 63 982 0
  | 4 => PA17TMRatArithmeticCachedOuter043.carryCap 63 2 PA17TMRatArithmeticWideCache045.allocationK
  | 5 => totalStates 63 (PA17TMRatArithmeticCachedPair054.cachedPairCap 1 1 0)
  | 6 => PA17TMRatArithmeticNativeTail055.carriedTailCap 63 3564 1
  | 7 => PA17TMRatArithmeticCachedOuter043.carryCap 63 3 PA17TMRatArithmeticWideCache045.allocationK
  | 8 => totalStates 63 (PA17TMRatArithmeticCachedPair054.cachedPairCap 2 2 0)
  | 9 => PA17TMRatArithmeticNativeTail055.carriedTailCap 63 1136 2
  | 10 => PA17TMRatArithmeticCachedOuter043.carryCap 63 4 PA17TMRatArithmeticWideCache045.allocationK
  | 11 => totalStates 63 (PA17TMRatArithmeticCachedPair054.cachedPairCap 3 2 1)
  | 12 => totalStates 63 1170
  | 13 => PA17TMRatArithmeticZeroCarry058.observeCap 1 4
  | 14 => PA17TMRatArithmeticCachedOuter043.carryCap 127 5 PA17TMRatArithmeticWideCache045.allocationK
  | 15 => totalStates 127 (PA17TMRatArithmeticCachedPair054.cachedReadyCap 4 1 0)
  | _ => PA17TMRatArithmeticSignDispatch053.dispatchCap 4

theorem component_states (phase : Fin 17) : (component phase).states=componentStates phase := by
  fin_cases phase <;> rfl

def commonCap : Nat := ∑ phase : Fin 17, componentStates phase

theorem commonCap_same : commonCap=∑ phase : Fin 17, (component phase).states := by
  apply Finset.sum_congr rfl
  intro phase _
  exact (component_states phase).symm

theorem component_fits (phase : Fin 17) : (component phase).states ≤ commonCap := by
  rw [component_states]
  exact Finset.single_le_sum (fun other _ => Nat.zero_le (componentStates other)) (Finset.mem_univ phase)

def controllerCap : Nat := totalStates 16 commonCap
attribute [local implicit_reducible] controllerCap

def controllerFamily (phase : Fin 17) : Machine commonCap :=
  padMachine (component_fits phase) (component phase).code

def nextPhase (phase : Fin 17) : Fin 17 := ⟨(phase.val+1)%17,Nat.mod_lt _ (by decide)⟩

def localCode (phase : Fin 17) (q : Fin (commonCap+1)) : Fin ((component phase).states+1) :=
  PA17TMRatArithmeticFirstRaw052.checkedIndex (component phase).states commonCap q

def controllerPorts (phase : Fin 17) (q : Fin (commonCap+1)) :
    Option (Fin 17 × Fin (commonCap+1)) :=
  if phase.val<16 then some (nextPhase phase,padLabel (component_fits (nextPhase phase))
    ((component (nextPhase phase)).entry ((component phase).decode (localCode phase q)))) else none

/-- No operand, sign, observed bit, record count, width or fuel is an
argument of this machine. All such observations arise in its actual run. -/
def mulMachine : Machine controllerCap := blockMachine controllerFamily controllerPorts

def liftCfg (phase : Fin 17) (state : MachineState (component phase).states) : MachineState controllerCap :=
  blockCfg phase (padCfg (component_fits phase) state)

def entryCfg (phase : Fin 17) (memory : Fin 128) (tape : Tape Bool) : MachineState controllerCap :=
  liftCfg phase ⟨(component phase).entry memory,tape⟩

def liftTrace (phase : Fin 17) (trace : List (MachineState (component phase).states)) :
    List (MachineState controllerCap) := trace.map (liftCfg phase)

theorem lift_tape (phase : Fin 17) (state : MachineState (component phase).states) :
    (liftCfg phase state).Tape=state.Tape := rfl

theorem entry_tape (phase : Fin 17) (memory : Fin 128) (tape : Tape Bool) :
    (entryCfg phase memory tape).Tape=tape := rfl

theorem liftTrace_length (phase : Fin 17) (trace : List (MachineState (component phase).states)) :
    (liftTrace phase trace).length=trace.length := List.length_map _

theorem nextPhase_value (phase : Fin 17) (h : phase.val<16) : (nextPhase phase).val=phase.val+1 := by
  apply Nat.mod_eq_of_lt
  omega

theorem localCode_pad (phase : Fin 17) (q : Fin ((component phase).states+1)) :
    localCode phase (padLabel (component_fits phase) q)=q :=
  PA17TMRatArithmeticFirstRaw052.checkedIndex_pad (component_fits phase) q


end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulController057
