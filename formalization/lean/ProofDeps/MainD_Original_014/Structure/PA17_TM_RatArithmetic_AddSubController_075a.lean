module
public import Structure.PA17_TM_RatArithmetic_AddSubPrefix_074a
public import Structure.PA17_TM_RatArithmetic_SignedSumFields_072a

/-! Fixed addition/subtraction control. The mode precedes all operands.
The two alternative cached-pair phases are selected by the actual saved
SX/SY row. The sign remap occurs only after real P-zero observation and
after the last use of the original denominator fields. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubController075

open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticMulController057 (Component row64Component row128Component
  row64_decode row128_decode widen64 narrow64 allocation64 allocation128 cached64 tail64)
open scoped BigOperators
attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticCachedOuter043.carryCap PA17TMRatArithmeticNativeTail055.carriedTailCap
  PA17TMRatArithmeticZeroCarry058.observeCap PA17TMRatArithmeticSignDispatch053.dispatchCap

def sameSignsFromMemory (subtract : Bool) (memory : Fin 64) : Bool :=
  memory.val.testBit 5==Bool.xor (memory.val.testBit 2) subtract

def repairedMemory (subtract : Bool) (memory : Fin 128) : Fin 128 :=
  widen64 (PA17TMRatArithmeticSignedSumFields072.selectedMemory subtract (narrow64 memory)
    (decide (memory.val/64=1)))

theorem actual_sameSigns (subtract : Bool) (x y : Rat) :
    sameSignsFromMemory subtract (PA17TMRatArithmeticMulStart049.actualMemory x y)=
      PA17TMRatArithmeticSignedSumFields072.sameSigns subtract x y := by
  have sx := (PA17TMRatArithmeticZeroCarry058.saved_sign_table
    (PA17TMRatArithmeticBookmark014.mNx x y) (PA17TMRatArithmeticParse002.sign x)).1
  have sy := (PA17TMRatArithmeticZeroCarry058.saved_sign_table
    (PA17TMRatArithmeticBookmark014.mNx x y) (PA17TMRatArithmeticParse002.sign x)).2.trans
    (PA17TMRatArithmeticBookmark014.observed_memory_bits x y).2.2.1
  change ((PA17TMRatArithmeticSignRead021.selectedMemory
      (PA17TMRatArithmeticBookmark014.mNx x y) (PA17TMRatArithmeticParse002.sign x)).val.testBit 5==
    Bool.xor ((PA17TMRatArithmeticSignRead021.selectedMemory
      (PA17TMRatArithmeticBookmark014.mNx x y) (PA17TMRatArithmeticParse002.sign x)).val.testBit 2) subtract)=_
  rw [sx,sy]
  rfl

theorem repaired_observed (subtract : Bool) (old : Fin 64) (pZero : Bool) :
    repairedMemory subtract (PA17TMRatArithmeticZeroCarry058.observedMemory old pZero)=
      widen64 (PA17TMRatArithmeticSignedSumFields072.selectedMemory subtract old pZero) := by
  have retained : narrow64 (PA17TMRatArithmeticZeroCarry058.observedMemory old pZero)=old := by
    apply Fin.ext
    exact PA17TMRatArithmeticZeroCarry058.observedMemory_retains_old old pZero
  unfold repairedMemory
  rw [retained,PA17TMRatArithmeticZeroCarry058.observedMemory_zero_bit]
  cases pZero <;> rfl

/-- Native Add has no home before the P-zero sensor. Its actual final
local label is arbitrary; the outer memory row is retained independently. -/
def addRecordFamily (_memory : Fin 64) : Machine 503 := PA17TMRatArithmeticNativeCache030.addCacheMachine
def addRecordPorts (_memory : Fin 64) (_q : Fin 504) : Option (Fin 64 × Fin 504) := none
def addRecordMachine : Machine (totalStates 63 503) := blockMachine addRecordFamily addRecordPorts
def addRecordComponent : Component := row64Component 503 addRecordMachine

theorem add_record_runs (memory : Fin 64) (first last : MachineState 503)
    (trace : List (MachineState 503))
    (run : PSTRTMSeq005.RunsFrom PA17TMRatArithmeticNativeCache030.addCacheMachine first trace last) :
    PSTRTMSeq005.RunsFrom addRecordMachine (blockCfg memory first)
      (trace.map (blockCfg (s:=503) memory)) (blockCfg memory last) :=
  block_runsFrom addRecordFamily addRecordPorts memory first last trace run rfl

theorem add_record_decode (memory : Fin 64) (actualLocal : Fin 504) :
    addRecordComponent.decode (label memory actualLocal)=widen64 memory :=
  row64_decode 503 addRecordMachine memory actualLocal

def observerMemory (sourceLater allLater : Nat)
    (q : Fin (PA17TMRatArithmeticZeroCarry058.observeCap sourceLater allLater+1)) : Fin 128 :=
  ⟨((phaseOf (p:=191) (s:=PA17TMRatArithmeticZeroCarry058.commonCap sourceLater allLater) q).val-64)%128,
    Nat.mod_lt _ (by decide)⟩

def observerComponent (sourceLater allLater : Nat) : Component :=
  ⟨PA17TMRatArithmeticZeroCarry058.observeCap sourceLater allLater,
    PA17TMRatArithmeticZeroCarry058.observeMachine sourceLater allLater,
    fun memory => PA17TMRatArithmeticZeroCarry058.observeEntry sourceLater allLater (narrow64 memory),
    observerMemory sourceLater allLater⟩

theorem observer_decode (sourceLater allLater : Nat) (memory : Fin 128) :
    observerMemory sourceLater allLater
      (PA17TMRatArithmeticZeroCarry058.observePort sourceLater allLater memory)=memory := by
  apply Fin.ext
  change ((phaseOf (label (PA17TMRatArithmeticZeroCarry058.newPhase memory)
    (padLabel (PA17TMRatArithmeticZeroCarry058.returnFits sourceLater allLater)
      (PA17TMRatArithmeticZeroCarry058.returnPort sourceLater allLater)))).val-64)%128=memory.val
  rw [phaseOf_label]
  change (64+memory.val-64)%128=memory.val
  rw [Nat.add_sub_cancel_left,Nat.mod_eq_of_lt memory.isLt]

def readyComponent : Component :=
  row128Component (PA17TMRatArithmeticCachedPair054.cachedReadyCap 8 1 0)
    (PA17TMRatArithmeticCachedPair054.cachedReadyMachine 127 8 1 0)

def outputComponent : Component :=
  ⟨PA17TMRatArithmeticSignDispatch053.dispatchCap 8,
    PA17TMRatArithmeticSignDispatch053.dispatchMachine 8 PA17TMRatArithmeticZeroCarry058.repairedNegative,
    PA17TMRatArithmeticSignDispatch053.dispatchEntry 8,fun _ => 0⟩

/-- The only alternatives are phases2/3. All remaining phases are shared.
Allocation counts are TOTAL; pair/home/output counts are LATER. -/
def component (phase : Fin 19) : Component :=
  match phase.val with
  | 0 => PA17TMRatArithmeticAddSubPrefix074.prefixComponent
  | 1 => allocation64 5
  | 2 => cached64 4 4 3
  | 3 => cached64 4 1 0
  | 4 => addRecordComponent
  | 5 => observerComponent 2 5
  | 6 => allocation64 6
  | 7 => cached64 5 0 3
  | 8 => tail64 ROOTTMGCDDispatch018.nativeGcdMachine 5
  | 9 => allocation64 7
  | 10 => cached64 6 1 0
  | 11 => tail64 PA17TMDivisionFull012.quotientMachine 6
  | 12 => allocation64 8
  | 13 => cached64 7 5 1
  | 14 => PA17TMRatArithmeticMulController057.quotientRecordComponent
  | 15 => observerComponent 1 8
  | 16 => allocation128 9
  | 17 => readyComponent
  | _ => outputComponent

/-- Pure Nat capacities, separate from all executable-code projections. -/
def componentStates (phase : Fin 19) : Nat :=
  match phase.val with
  | 0 => PA17TMRatArithmeticAddSubPrefix074.prefixCap
  | 1 => PA17TMRatArithmeticCachedOuter043.carryCap 63 5 PA17TMRatArithmeticWideCache045.allocationK
  | 2 => totalStates 63 (PA17TMRatArithmeticCachedPair054.cachedPairCap 4 4 3)
  | 3 => totalStates 63 (PA17TMRatArithmeticCachedPair054.cachedPairCap 4 1 0)
  | 4 => totalStates 63 503
  | 5 => PA17TMRatArithmeticZeroCarry058.observeCap 2 5
  | 6 => PA17TMRatArithmeticCachedOuter043.carryCap 63 6 PA17TMRatArithmeticWideCache045.allocationK
  | 7 => totalStates 63 (PA17TMRatArithmeticCachedPair054.cachedPairCap 5 0 3)
  | 8 => PA17TMRatArithmeticNativeTail055.carriedTailCap 63 3564 5
  | 9 => PA17TMRatArithmeticCachedOuter043.carryCap 63 7 PA17TMRatArithmeticWideCache045.allocationK
  | 10 => totalStates 63 (PA17TMRatArithmeticCachedPair054.cachedPairCap 6 1 0)
  | 11 => PA17TMRatArithmeticNativeTail055.carriedTailCap 63 1136 6
  | 12 => PA17TMRatArithmeticCachedOuter043.carryCap 63 8 PA17TMRatArithmeticWideCache045.allocationK
  | 13 => totalStates 63 (PA17TMRatArithmeticCachedPair054.cachedPairCap 7 5 1)
  | 14 => totalStates 63 1170
  | 15 => PA17TMRatArithmeticZeroCarry058.observeCap 1 8
  | 16 => PA17TMRatArithmeticCachedOuter043.carryCap 127 9 PA17TMRatArithmeticWideCache045.allocationK
  | 17 => totalStates 127 (PA17TMRatArithmeticCachedPair054.cachedReadyCap 8 1 0)
  | _ => PA17TMRatArithmeticSignDispatch053.dispatchCap 8

theorem component_states (phase : Fin 19) : (component phase).states=componentStates phase := by
  fin_cases phase <;> rfl

def commonCap : Nat := ∑ phase : Fin 19, componentStates phase
def controllerCap : Nat := totalStates 18 commonCap
attribute [local implicit_reducible] controllerCap

theorem component_fits (phase : Fin 19) : (component phase).states≤commonCap := by
  rw [component_states]
  exact Finset.single_le_sum (fun other _ => Nat.zero_le (componentStates other)) (Finset.mem_univ phase)

def family (phase : Fin 19) : Machine commonCap := padMachine (component_fits phase) (component phase).code
def localCode (phase : Fin 19) (q : Fin (commonCap+1)) : Fin ((component phase).states+1) :=
  PA17TMRatArithmeticFirstRaw052.checkedIndex (component phase).states commonCap q

def nextPhase (subtract : Bool) (phase : Fin 19) (memory : Fin 128) : Fin 19 :=
  if phase.val=1 then (if sameSignsFromMemory subtract (narrow64 memory) then 2 else 3)
  else if phase.val=2 then 4
  else ⟨(phase.val+1)%19,Nat.mod_lt _ (by decide)⟩

def nextMemory (subtract : Bool) (phase : Fin 19) (memory : Fin 128) : Fin 128 :=
  if phase.val=5 then repairedMemory subtract memory else memory

def ports (subtract : Bool) (phase : Fin 19) (q : Fin (commonCap+1)) :
    Option (Fin 19 × Fin (commonCap+1)) :=
  if phase.val<18 then
    let memory := (component phase).decode (localCode phase q)
    let target := nextPhase subtract phase memory
    some (target,padLabel (component_fits target) ((component target).entry (nextMemory subtract phase memory)))
  else none

/-- The mode is fixed before all rational inputs. No tape value, sign,
observed flag, width, room, fuel or answer is supplied to this code. -/
def addSubMachine (subtract : Bool) : Machine controllerCap := blockMachine family (ports subtract)

def liftCfg (phase : Fin 19) (state : MachineState (component phase).states) : MachineState controllerCap :=
  blockCfg phase (padCfg (component_fits phase) state)
def entryCfg (phase : Fin 19) (memory : Fin 128) (tape : Tape Bool) : MachineState controllerCap :=
  liftCfg phase ⟨(component phase).entry memory,tape⟩
def liftTrace (phase : Fin 19) (trace : List (MachineState (component phase).states)) :
    List (MachineState controllerCap) := trace.map (liftCfg phase)

theorem liftTrace_length (phase : Fin 19) (trace : List (MachineState (component phase).states)) :
    (liftTrace phase trace).length=trace.length := List.length_map _
theorem lift_tape (phase : Fin 19) (state : MachineState (component phase).states) :
    (liftCfg phase state).Tape=state.Tape := rfl
theorem entry_tape (phase : Fin 19) (memory : Fin 128) (tape : Tape Bool) :
    (entryCfg phase memory tape).Tape=tape := rfl
theorem localCode_pad (phase : Fin 19) (q : Fin ((component phase).states+1)) :
    localCode phase (padLabel (component_fits phase) q)=q :=
  PA17TMRatArithmeticFirstRaw052.checkedIndex_pad (component_fits phase) q

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAddSubController075
