module
public import Structure.PA17_TM_RatArithmetic_EraseBank_034a

/-! Static reverse erasure. The already-erased later records are retained
as an actual FALSE suffix while the next older record is really erased. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticEraseBank034

open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticRecordNav032
open PA17TMRatArithmeticBankWalk033

def totalSpan : List RecordSpec → Nat
  | [] => 0
  | record::later => oneSpan record.gap record.digits+totalSpan later

def erasedBankTape (archive : List Bool) (records : List RecordSpec) (suffix : List Bool) : Tape Bool :=
  Tape.mk₂ archive (true::(List.replicate (totalSpan records) false++suffix))

private theorem erasedBank_cons (archive : List Bool) (record : RecordSpec) (later : List RecordSpec)
    (suffix : List Bool) :
    erasedBankTape archive (record::later) suffix =
      eraseOneOutput record.gap archive record.digits (List.replicate (totalSpan later) false++suffix) := by
  change Tape.mk₂ archive (true::(List.replicate (oneSpan record.gap record.digits+totalSpan later) false++suffix)) =
    Tape.mk₂ archive (true::(List.replicate (oneSpan record.gap record.digits) false++
      (List.replicate (totalSpan later) false++suffix)))
  rw [List.replicate_add,List.append_assoc]

def eraseCap : Nat → Nat
  | 0 => 0
  | j+1 => eraseCap j+25+1

/-- Only compiled j selects code. Record/gap/digit metadata is not an
executable argument or a new original input field. -/
def eraseBankMachine : (j : Nat) → Machine (eraseCap j)
  | 0 => identityMachine
  | j+1 => PSTRTMSeq005.seqMachine (eraseBankMachine j) eraseOneMachine

def eraseBankPort : (j : Nat) → Fin (eraseCap j+1)
  | 0 => 0
  | j+1 => PSTRTMSeq005.rightLabel (a:=eraseCap j) (25 : Fin 26)

def eraseFee : List RecordSpec → Nat
  | [] => 1
  | record::later => eraseFee later+(record.gap+8*record.digits.length+28)

theorem erase_records (records : List RecordSpec) (archive suffix : List Bool) :
    BoundedRun (s:=eraseCap records.length) (eraseBankMachine records.length)
      (bankEnd archive records suffix) (eraseBankPort records.length)
      (erasedBankTape archive records suffix) (eraseFee records) := by
  induction records generalizing archive with
  | nil => exact identity_bounded (Tape.mk₂ archive (true::suffix))
  | cons record later ih =>
    have he := eraseOne_bounded record.gap archive record.digits
      (List.replicate (totalSpan later) false++suffix)
    have h := (ih (recordLeft record.gap archive true record.digits)).seq he
    rw [←erasedBank_cons archive record later suffix] at h
    exact h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticEraseBank034
