module
public import Structure.PA17_TM_RatArithmetic_CachedOuter_043d

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedOuter043
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedPass036

def carryCap (p j k : Nat) : Nat := totalStates p (outerCap j k)
attribute [local implicit_reducible] carryCap

def carryFamily (p j k : Nat) (_memory : Fin (p+1)) : Machine (outerCap j k) := outerMachine j k
def carryPorts (p j k : Nat) (_memory : Fin (p+1)) (_local : Fin (outerCap j k+1)) :
    Option (Fin (p+1) × Fin (outerCap j k+1)) := none
def carryMachine (p j k : Nat) : Machine (carryCap p j k) := blockMachine (carryFamily p j k) (carryPorts p j k)

def carryEntry (p j k : Nat) (memory : Fin (p+1)) (tape : Tape Bool) : MachineState (carryCap p j k) :=
  blockCfg (s:=outerCap j k) memory ⟨0,tape⟩
def carryFinal (p j k : Nat) (memory : Fin (p+1)) (tape : Tape Bool) : MachineState (carryCap p j k) :=
  blockCfg (s:=outerCap j k) memory ⟨outerPort j k,tape⟩

theorem carryEntry_value (p j k : Nat) (memory : Fin (p+1)) (tape : Tape Bool) :
    (carryEntry p j k memory tape).q.val=memory.val*(outerCap j k+1) := by
  simp [carryEntry,blockCfg,label]

theorem carryFinal_value (p j k : Nat) (memory : Fin (p+1)) (tape : Tape Bool) :
    (carryFinal p j k memory tape).q.val=memory.val*(outerCap j k+1)+(22*j+728) := by
  change memory.val*(outerCap j k+1)+(outerPort j k).val=_
  rw [outerPort_value]

/-- Every row contains the same tape/counter program. All rows are
compiled before actual inputs; a caller's already-observed control bits
remain in its real row. No host memory tuple or phase-zero reset occurs. -/
theorem original_carry_runsFrom (p j k : Nat) (memory : Fin (p+1))
    (records : List RecordSpec) (hj : records.length=j) (x y : Rat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (carryMachine p j k)
      (carryEntry p j k memory (Tape.mk₂ [false]
        (prefixRight (sign x) (originalBank x y (bankTail records []))))) trace
      (carryFinal p j k memory (Tape.mk₂ [false] (prefixRight (sign x)
        (originalBank x y (cachedTail records (k*(fieldWidth x y)^2)))))) ∧
      trace.length≤outerFee j k records (fieldWidth x y) := by
  obtain ⟨trace,hr,hl⟩ := original_outer_bounded j k records hj x y
  have hs := block_segment (carryFamily p j k) (carryPorts p j k) memory _ _ _ hr
  refine ⟨trace.map (blockCfg (s:=outerCap j k) memory),⟨hs.1,hs.2.1,hs.2.2,?_⟩,?_⟩
  · exact block_halt (carryFamily p j k) (carryPorts p j k) memory _ hr.2.2.2 rfl
  · simpa only [List.length_map] using hl

theorem original_carry_contract (p j k : Nat) (memory : Fin (p+1))
    (records : List RecordSpec) (hj : records.length=j) (x y : Rat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (carryMachine p j k)
      (carryEntry p j k memory (Tape.mk₂ [false]
        (prefixRight (sign x) (originalBank x y (bankTail records []))))) trace
      (carryFinal p j k memory (Tape.mk₂ [false] (prefixRight (sign x)
        (originalBank x y (cachedTail records (k*(fieldWidth x y)^2)))))) ∧
      trace.length≤outerFee j k records (fieldWidth x y) ∧
      ∀ prefixLength, visitedSpace (carryMachine p j k) (encode [.rational x,.rational y]).length
        (trace.take prefixLength) ≤
        (encode [.rational x,.rational y]).length+2*outerFee j k records (fieldWidth x y)+1 := by
  obtain ⟨trace,hr,hl⟩ := original_carry_runsFrom p j k memory records hj x y
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength
  have hs := PSTRTMTrace002.visitedSpace_le (carryMachine p j k)
    (encode [.rational x,.rational y]).length (trace.take prefixLength)
  have hp : (trace.take prefixLength).length≤trace.length := by simp only [List.length_take];omega
  omega

def carry32Machine (j k : Nat) : Machine (carryCap 31 j k) := carryMachine 31 j k
def carry64Machine (j k : Nat) : Machine (carryCap 63 j k) := carryMachine 63 j k

theorem carry32_runsFrom (j k : Nat) (memory : Fin 32) (records : List RecordSpec)
    (hj : records.length=j) (x y : Rat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (carry32Machine j k)
      (carryEntry 31 j k memory (Tape.mk₂ [false]
        (prefixRight (sign x) (originalBank x y (bankTail records []))))) trace
      (carryFinal 31 j k memory (Tape.mk₂ [false] (prefixRight (sign x)
        (originalBank x y (cachedTail records (k*(fieldWidth x y)^2)))))) ∧
      trace.length≤outerFee j k records (fieldWidth x y) :=
  original_carry_runsFrom 31 j k memory records hj x y

theorem carry64_runsFrom (j k : Nat) (memory : Fin 64) (records : List RecordSpec)
    (hj : records.length=j) (x y : Rat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (carry64Machine j k)
      (carryEntry 63 j k memory (Tape.mk₂ [false]
        (prefixRight (sign x) (originalBank x y (bankTail records []))))) trace
      (carryFinal 63 j k memory (Tape.mk₂ [false] (prefixRight (sign x)
        (originalBank x y (cachedTail records (k*(fieldWidth x y)^2)))))) ∧
      trace.length≤outerFee j k records (fieldWidth x y) :=
  original_carry_runsFrom 63 j k memory records hj x y

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedOuter043
