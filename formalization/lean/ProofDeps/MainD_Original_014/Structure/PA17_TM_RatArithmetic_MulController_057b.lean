module
public import Structure.PA17_TM_RatArithmetic_FirstRaw_052c
public import Structure.PA17_TM_RatArithmetic_CachedOuter_043e
public import Structure.PA17_TM_RatArithmetic_CachedPair_054f
public import Structure.PA17_TM_RatArithmetic_NativeTail_055c
public import Structure.PA17_TM_RatArithmetic_ZeroCarry_058e
public import Structure.PA17_TM_RatArithmetic_SignDispatch_053b

/-! Fixed finite components and checked decoders of their actual local HALT labels. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulController057

open Turing PA17TMDivisionCompose006
open scoped BigOperators
attribute [local implicit_reducible] totalStates
  PA17TMRatArithmeticFirstRaw052.firstCap PA17TMRatArithmeticFirstRaw052.bridgeCap
  PA17TMRatArithmeticFirstRaw052.commonCap PA17TMRatArithmeticFirstMul051.cycleCap
  PA17TMRatArithmeticCachedOuter043.carryCap PA17TMRatArithmeticNativeTail055.carriedTailCap
  PA17TMRatArithmeticZeroCarry058.observeCap PA17TMRatArithmeticSignDispatch053.dispatchCap

def widen64 (memory : Fin 64) : Fin 128 := ⟨memory.val,by have h:=memory.isLt;omega⟩

def narrow64 (memory : Fin 128) : Fin 64 := ⟨memory.val%64,Nat.mod_lt _ (by decide)⟩

theorem narrow_widen (memory : Fin 64) : narrow64 (widen64 memory)=memory := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt memory.isLt

/-- Only fixed finite control tables; no tape value, gap, width or answer
is a field of this executable component. -/
structure Component where
  states : Nat
  code : Machine states
  entry : Fin 128 → Fin (states+1)
  decode : Fin (states+1) → Fin 128

def row64Component (states : Nat) (code : Machine (totalStates 63 states)) : Component :=
  ⟨totalStates 63 states,code,
    fun memory => label (narrow64 memory) (0 : Fin (states+1)),
    fun q => widen64 (phaseOf (p:=63) (s:=states) q)⟩

def row128Component (states : Nat) (code : Machine (totalStates 127 states)) : Component :=
  ⟨totalStates 127 states,code,
    fun memory => label memory (0 : Fin (states+1)),
    fun q => phaseOf (p:=127) (s:=states) q⟩

theorem row64_decode (states : Nat) (code : Machine (totalStates 63 states))
    (memory : Fin 64) (q : Fin (states+1)) :
    (row64Component states code).decode (label memory q)=widen64 memory := by
  exact congrArg widen64 (phaseOf_label memory q)

theorem row64_entry (states : Nat) (code : Machine (totalStates 63 states)) (memory : Fin 64) :
    (row64Component states code).entry (widen64 memory)=label memory (0 : Fin (states+1)) := by
  change label (narrow64 (widen64 memory)) (0 : Fin (states+1))=_
  rw [narrow_widen]

theorem row128_decode (states : Nat) (code : Machine (totalStates 127 states))
    (memory : Fin 128) (q : Fin (states+1)) :
    (row128Component states code).decode (label memory q)=memory := phaseOf_label memory q

/-- Decode with opaque generic capacities before specializing the very
large052 prefix capacity. No closed machine or concrete modulus unfolds. -/
def nestedRow64Decode (rowStates shared : Nat) (q : Fin (totalStates 1 shared+1)) : Fin 128 :=
  widen64 (phaseOf (p:=63) (s:=rowStates)
    (PA17TMRatArithmeticFirstRaw052.checkedIndex (totalStates 63 rowStates) shared
      (localOf (p:=1) (s:=shared) q)))

theorem nestedRow64_decode (rowStates shared : Nat) (fits : totalStates 63 rowStates ≤ shared)
    (memory : Fin 64) (q : Fin (rowStates+1)) :
    nestedRow64Decode rowStates shared (label (1 : Fin 2) (padLabel fits (label memory q)))=
      widen64 memory := by
  simp only [nestedRow64Decode,localOf_label,PA17TMRatArithmeticFirstRaw052.checkedIndex_pad,phaseOf_label]

def firstDecode (q : Fin (PA17TMRatArithmeticFirstRaw052.firstCap+1)) : Fin 128 :=
  nestedRow64Decode 2078
    (PA17TMRatArithmeticFirstRaw052.commonCap PA17TMRatArithmeticWideCache045.allocationK
      (PA17TMRatArithmeticFirstMul051.cycleCap 63)) q

def firstComponent : Component :=
  ⟨PA17TMRatArithmeticFirstRaw052.firstCap,PA17TMRatArithmeticFirstRaw052.firstMachine,
    fun _ => 0,firstDecode⟩

theorem first_decode (memory : Fin 64) (tape : Tape Bool) :
    firstDecode (PA17TMRatArithmeticFirstRaw052.consumerState
      PA17TMRatArithmeticWideCache045.allocationK (PA17TMRatArithmeticFirstMul051.cycleCap 63)
      (PA17TMRatArithmeticFirstMul051.cyclePort 63 memory) tape).q=widen64 memory := by
  exact nestedRow64_decode 2078 _
    (PA17TMRatArithmeticFirstRaw052.consumer_le_common _ _) memory PA17TMRatArithmeticFirstMul051.cycleRowPort

def allocation64 (total : Nat) : Component :=
  row64Component (PA17TMRatArithmeticCachedOuter043.outerCap total PA17TMRatArithmeticWideCache045.allocationK)
    (PA17TMRatArithmeticCachedOuter043.carryMachine 63 total PA17TMRatArithmeticWideCache045.allocationK)

def allocation128 (total : Nat) : Component :=
  row128Component (PA17TMRatArithmeticCachedOuter043.outerCap total PA17TMRatArithmeticWideCache045.allocationK)
    (PA17TMRatArithmeticCachedOuter043.carryMachine 127 total PA17TMRatArithmeticWideCache045.allocationK)

def denominators : Component :=
  row64Component (PA17TMRatArithmeticCachedPair054.originalPairCap 0)
    (PA17TMRatArithmeticCachedPair054.originalPairMachine 63 .dx .dy 0)

def tail64 {states : Nat} (native : Machine states) (later : Nat) : Component :=
  row64Component (PA17TMRatArithmeticNativeTail055.tailCap states later)
    (PA17TMRatArithmeticNativeTail055.carriedTailMachine 63 native later)

def cached64 (later aLater bLater : Nat) : Component :=
  row64Component (PA17TMRatArithmeticCachedPair054.cachedPairCap later aLater bLater)
    (PA17TMRatArithmeticCachedPair054.cachedPairMachine 63 later aLater bLater)

def ready128 : Component :=
  row128Component (PA17TMRatArithmeticCachedPair054.cachedReadyCap 4 1 0)
    (PA17TMRatArithmeticCachedPair054.cachedReadyMachine 127 4 1 0)

/-- The last quotient record deliberately has no home program. Its actual
native final local label remains arbitrary inside the unchanged outer row. -/
def quotientRecordFamily (_memory : Fin 64) : Machine 1170 :=
  PA17TMRatArithmeticNativeCache030.quotientCacheMachine

def quotientRecordPorts (_memory : Fin 64) (_q : Fin 1171) : Option (Fin 64 × Fin 1171) := none

def quotientRecordMachine : Machine (totalStates 63 1170) :=
  blockMachine quotientRecordFamily quotientRecordPorts

def quotientRecordComponent : Component := row64Component 1170 quotientRecordMachine

theorem quotient_record_runs (memory : Fin 64) (first last : MachineState 1170)
    (trace : List (MachineState 1170))
    (run : PSTRTMSeq005.RunsFrom PA17TMRatArithmeticNativeCache030.quotientCacheMachine first trace last) :
    PSTRTMSeq005.RunsFrom quotientRecordMachine (blockCfg memory first)
      (trace.map (blockCfg (s:=1170) memory)) (blockCfg memory last) :=
  block_runsFrom quotientRecordFamily quotientRecordPorts memory first last trace run rfl

theorem quotient_record_decode (memory : Fin 64) (actualLocal : Fin 1171) :
    quotientRecordComponent.decode (label memory actualLocal)=widen64 memory :=
  row64_decode 1170 quotientRecordMachine memory actualLocal

def zeroDecode (q : Fin (PA17TMRatArithmeticZeroCarry058.observeCap 1 4+1)) : Fin 128 :=
  ⟨((phaseOf (p:=191) (s:=PA17TMRatArithmeticZeroCarry058.commonCap 1 4) q).val-64)%128,
    Nat.mod_lt _ (by decide)⟩

def zeroComponent : Component :=
  ⟨PA17TMRatArithmeticZeroCarry058.observeCap 1 4,PA17TMRatArithmeticZeroCarry058.observeMachine 1 4,
    fun memory => PA17TMRatArithmeticZeroCarry058.observeEntry 1 4 (narrow64 memory),zeroDecode⟩

theorem zero_decode (memory : Fin 128) :
    zeroDecode (PA17TMRatArithmeticZeroCarry058.observePort 1 4 memory)=memory := by
  apply Fin.ext
  change ((phaseOf (label (PA17TMRatArithmeticZeroCarry058.newPhase memory)
    (padLabel (PA17TMRatArithmeticZeroCarry058.returnFits 1 4)
      (PA17TMRatArithmeticZeroCarry058.returnPort 1 4)))).val-64)%128=memory.val
  rw [phaseOf_label]
  change (64+memory.val-64)%128=memory.val
  rw [Nat.add_sub_cancel_left,Nat.mod_eq_of_lt memory.isLt]

def outputComponent : Component :=
  ⟨PA17TMRatArithmeticSignDispatch053.dispatchCap 4,
    PA17TMRatArithmeticSignDispatch053.dispatchMachine 4 PA17TMRatArithmeticZeroCarry058.repairedNegative,
    PA17TMRatArithmeticSignDispatch053.dispatchEntry 4,fun _ => 0⟩


end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulController057
