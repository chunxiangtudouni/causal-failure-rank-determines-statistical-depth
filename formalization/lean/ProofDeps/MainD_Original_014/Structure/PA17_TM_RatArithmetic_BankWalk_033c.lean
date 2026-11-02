module
public import Structure.PA17_TM_RatArithmetic_BankWalk_033b

/-! The SAME frozen forward program accepts any actual old bit, including
the original FALSE footer. Only the first record differs; later ends are TRUE.
No FALSE-boundary backwards scan is asserted. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankWalk033

open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticRecordNav032

def bankLeftAny (oldBit : Bool) (archive : List Bool) : List RecordSpec → List Bool
  | [] => archive
  | record::later => bankLeft (recordLeft record.gap archive oldBit record.digits) later

def bankEndBitAny (oldBit : Bool) : List RecordSpec → Bool
  | [] => oldBit
  | _::_ => true

def bankStartAny (oldBit : Bool) (archive : List Bool) (records : List RecordSpec)
    (suffix : List Bool) : Tape Bool := Tape.mk₂ archive (oldBit::bankTail records suffix)

def bankEndAny (oldBit : Bool) (archive : List Bool) (records : List RecordSpec)
    (suffix : List Bool) : Tape Bool :=
  Tape.mk₂ (bankLeftAny oldBit archive records) (bankEndBitAny oldBit records::suffix)

theorem forwardAny_records (oldBit : Bool) (records : List RecordSpec) (archive suffix : List Bool) :
    BoundedRun (s:=forwardCap records.length) (forwardMachine records.length)
      (bankStartAny oldBit archive records suffix) (forwardPort records.length)
      (bankEndAny oldBit archive records suffix) (forwardFee records) := by
  cases records with
  | nil => exact identity_bounded (Tape.mk₂ archive (oldBit::suffix))
  | cons record later =>
    have hn := recordNext_bounded record.gap archive oldBit record.digits (bankTail later suffix)
    exact hn.seq (forward_records later (recordLeft record.gap archive oldBit record.digits) suffix)

/-- j is the already-frozen code constant before all actual old-bit/bank
values. The code and every frozen a/b product remain exactly unchanged. -/
theorem forwardAny_bounded (j : Nat) (oldBit : Bool) (records : List RecordSpec)
    (hj : records.length=j) (archive suffix : List Bool) :
    BoundedRun (s:=forwardCap j) (forwardMachine j) (bankStartAny oldBit archive records suffix)
      (forwardPort j) (bankEndAny oldBit archive records suffix)
      (totalGap records+2*totalWidth records+9*j+1) := by
  have h := forwardAny_records oldBit records archive suffix
  rw [hj] at h
  simpa only [forwardFee_eq,hj] using h

/-- Whole Tape preserves the initial FALSE or TRUE bit in its real cell.
For zero records the genuine identity HALT keeps that same bit under the head;
for positive records the final head is the last actual TRUE end marker. -/
theorem forwardAny_contract (j : Nat) (oldBit : Bool) (records : List RecordSpec)
    (hj : records.length=j) (archive suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (forwardMachine j)
        ⟨0,bankStartAny oldBit archive records suffix⟩ trace
        ⟨forwardPort j,bankEndAny oldBit archive records suffix⟩ ∧
      trace.length≤totalGap records+2*totalWidth records+9*j+1 ∧
      ∀ prefixLength chargedL, visitedSpace (forwardMachine j) chargedL (trace.take prefixLength) ≤
        chargedL+2*totalGap records+4*totalWidth records+18*j+3 := by
  obtain ⟨trace,hr,hl⟩ := forwardAny_bounded j oldBit records hj archive suffix
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le (forwardMachine j) chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankWalk033
