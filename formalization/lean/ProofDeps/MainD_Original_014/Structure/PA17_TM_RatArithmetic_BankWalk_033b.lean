module
public import Structure.PA17_TM_RatArithmetic_BankWalk_033a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankWalk033

open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def totalGap : List RecordSpec → Nat
  | [] => 0
  | record::later => record.gap+totalGap later

def totalWidth : List RecordSpec → Nat
  | [] => 0
  | record::later => record.digits.length+totalWidth later

theorem forwardCap_eq (j : Nat) : forwardCap j=9*j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [forwardCap,ih];omega

theorem backwardCap_eq (j : Nat) : backwardCap j=13*j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [backwardCap,ih];omega

theorem forwardFee_eq (records : List RecordSpec) :
    forwardFee records=totalGap records+2*totalWidth records+9*records.length+1 := by
  induction records with
  | nil => rfl
  | cons record later ih =>
    simp only [forwardFee,totalGap,totalWidth,List.length_cons,ih]
    omega

theorem backwardFee_eq (records : List RecordSpec) :
    backwardFee records=totalGap records+2*totalWidth records+12*records.length+1 := by
  induction records with
  | nil => rfl
  | cons record later ih =>
    simp only [backwardFee,totalGap,totalWidth,List.length_cons,ih]
    omega

/-- Fixed j comes BEFORE all bank metadata. The structural length equality
describes the actual bank, not a runtime field or a host choice by Rat values. -/
theorem forward_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive suffix : List Bool) :
    BoundedRun (forwardMachine j) (bankStart archive records suffix) (forwardPort j)
      (bankEnd archive records suffix) (totalGap records+2*totalWidth records+9*j+1) := by
  have h := forward_records records archive suffix
  rw [hj] at h
  simpa only [forwardFee_eq,hj] using h

theorem backward_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive suffix : List Bool) :
    BoundedRun (backwardMachine j) (bankEnd archive records suffix) (backwardPort j)
      (bankStart archive records suffix) (totalGap records+2*totalWidth records+12*j+1) := by
  have h := backward_records records archive suffix
  rw [hj] at h
  simpa only [backwardFee_eq,hj] using h

def roundCap : Nat → Nat
  | 0 => 0
  | j+1 => forwardCap (j+1)+backwardCap (j+1)+1

/-- TRUE-marker round trip. The zero-count program is the real identity
HALT; positive counts use only the actual frozen Seq compiler and cursors. -/
def roundMachine : (j : Nat) → Machine (roundCap j)
  | 0 => identityMachine
  | j+1 => PSTRTMSeq005.seqMachine (forwardMachine (j+1)) (backwardMachine (j+1))

def roundPort : (j : Nat) → Fin (roundCap j+1)
  | 0 => 0
  | j+1 => PSTRTMSeq005.rightLabel (a:=forwardCap (j+1)) (backwardPort (j+1))

theorem roundCap_positive (j : Nat) : roundCap (j+1)=22*(j+1)+1 := by
  simp only [roundCap,forwardCap_eq,backwardCap_eq]
  omega

theorem round_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive suffix : List Bool) :
    BoundedRun (roundMachine j) (bankStart archive records suffix) (roundPort j)
      (bankStart archive records suffix) (2*totalGap records+4*totalWidth records+21*j+2) := by
  cases j with
  | zero =>
    cases records with
    | nil => exact (identity_bounded (Tape.mk₂ archive (true::suffix))).mono (by decide)
    | cons record later => simp at hj
  | succ j =>
    have h := (forward_bounded (j+1) records hj archive suffix).seq
      (backward_bounded (j+1) records hj archive suffix)
    apply h.mono
    omega

theorem forward_contract (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (forwardMachine j) ⟨0,bankStart archive records suffix⟩ trace
        ⟨forwardPort j,bankEnd archive records suffix⟩ ∧
      trace.length≤totalGap records+2*totalWidth records+9*j+1 ∧
      ∀ prefixLength chargedL, visitedSpace (forwardMachine j) chargedL (trace.take prefixLength) ≤
        chargedL+2*totalGap records+4*totalWidth records+18*j+3 := by
  obtain ⟨trace,hr,hl⟩ := forward_bounded j records hj archive suffix
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le (forwardMachine j) chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

theorem backward_contract (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (backwardMachine j) ⟨0,bankEnd archive records suffix⟩ trace
        ⟨backwardPort j,bankStart archive records suffix⟩ ∧
      trace.length≤totalGap records+2*totalWidth records+12*j+1 ∧
      ∀ prefixLength chargedL, visitedSpace (backwardMachine j) chargedL (trace.take prefixLength) ≤
        chargedL+2*totalGap records+4*totalWidth records+24*j+3 := by
  obtain ⟨trace,hr,hl⟩ := backward_bounded j records hj archive suffix
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le (backwardMachine j) chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

/-- The SAME actual round-trip trace returns the head and entire Tape;
the arbitrary archive, all records/markers/END00 and suffix are unchanged. -/
theorem round_contract (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (roundMachine j) ⟨0,bankStart archive records suffix⟩ trace
        ⟨roundPort j,bankStart archive records suffix⟩ ∧
      trace.length≤2*totalGap records+4*totalWidth records+21*j+2 ∧
      ∀ prefixLength chargedL, visitedSpace (roundMachine j) chargedL (trace.take prefixLength) ≤
        chargedL+4*totalGap records+8*totalWidth records+42*j+5 := by
  obtain ⟨trace,hr,hl⟩ := round_bounded j records hj archive suffix
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le (roundMachine j) chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBankWalk033
