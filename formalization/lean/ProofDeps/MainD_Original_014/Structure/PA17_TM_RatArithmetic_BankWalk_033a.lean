module
public import Structure.PA17_TM_RatArithmetic_RecordNav_032b

/-! Static repetition of the frozen actual record cursors. RecordSpec is
physical proof metadata; executable code depends only on compiled count j. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankWalk033

open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticRecordNav032

structure RecordSpec where
  gap : Nat
  digits : List Bool

def bankTail : List RecordSpec → List Bool → List Bool
  | [], suffix => suffix
  | record::later, suffix => List.replicate record.gap false++true::false::
      recordWord record.digits (bankTail later suffix)

def bankLeft (archive : List Bool) : List RecordSpec → List Bool
  | [] => archive
  | record::later => bankLeft (recordLeft record.gap archive true record.digits) later

def bankStart (archive : List Bool) (records : List RecordSpec) (suffix : List Bool) : Tape Bool :=
  Tape.mk₂ archive (true::bankTail records suffix)

def bankEnd (archive : List Bool) (records : List RecordSpec) (suffix : List Bool) : Tape Bool :=
  Tape.mk₂ (bankLeft archive records) (true::suffix)

def identityMachine : Machine 0 := fun _ _ => none

theorem identity_bounded (tape : Tape Bool) : BoundedRun identityMachine tape 0 tape 1 := by
  exact ⟨[⟨0,tape⟩],⟨rfl,by simp,rfl,rfl⟩,by rfl⟩

def forwardCap : Nat → Nat
  | 0 => 0
  | j+1 => 8+forwardCap j+1

def backwardCap : Nat → Nat
  | 0 => 0
  | j+1 => backwardCap j+12+1

/-- j is a compile-time constant. No record, gap, digit or Rat value is
an executable parameter. The base program genuinely HALTs without moving. -/
def forwardMachine : (j : Nat) → Machine (forwardCap j)
  | 0 => identityMachine
  | j+1 => PSTRTMSeq005.seqMachine recordNextMachine (forwardMachine j)

def backwardMachine : (j : Nat) → Machine (backwardCap j)
  | 0 => identityMachine
  | j+1 => PSTRTMSeq005.seqMachine (backwardMachine j) recordPrevMachine

def forwardPort : (j : Nat) → Fin (forwardCap j+1)
  | 0 => 0
  | j+1 => PSTRTMSeq005.rightLabel (a:=8) (forwardPort j)

def backwardPort : (j : Nat) → Fin (backwardCap j+1)
  | 0 => 0
  | j+1 => PSTRTMSeq005.rightLabel (a:=backwardCap j) (12 : Fin 13)

def forwardFee : List RecordSpec → Nat
  | [] => 1
  | record::later => record.gap+2*record.digits.length+9+forwardFee later

def backwardFee : List RecordSpec → Nat
  | [] => 1
  | record::later => backwardFee later+(record.gap+2*record.digits.length+12)

theorem forward_records (records : List RecordSpec) (archive suffix : List Bool) :
    BoundedRun (forwardMachine records.length) (bankStart archive records suffix)
      (forwardPort records.length) (bankEnd archive records suffix) (forwardFee records) := by
  induction records generalizing archive with
  | nil => exact identity_bounded (Tape.mk₂ archive (true::suffix))
  | cons record later ih =>
    have hn := recordNext_bounded record.gap archive true record.digits (bankTail later suffix)
    exact hn.seq (ih (recordLeft record.gap archive true record.digits))

theorem backward_records (records : List RecordSpec) (archive suffix : List Bool) :
    BoundedRun (backwardMachine records.length) (bankEnd archive records suffix)
      (backwardPort records.length) (bankStart archive records suffix) (backwardFee records) := by
  induction records generalizing archive with
  | nil => exact identity_bounded (Tape.mk₂ archive (true::suffix))
  | cons record later ih =>
    have hp := recordPrev_bounded record.gap archive record.digits (bankTail later suffix)
    exact (ih (recordLeft record.gap archive true record.digits)).seq hp

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankWalk033
