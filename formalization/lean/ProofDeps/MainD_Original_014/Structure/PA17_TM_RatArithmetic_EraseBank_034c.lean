module
public import Structure.PA17_TM_RatArithmetic_EraseBank_034b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticEraseBank034

open Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033

theorem eraseCap_eq (j : Nat) : eraseCap j=26*j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [eraseCap,ih];omega

theorem totalSpan_eq (records : List RecordSpec) :
    totalSpan records=totalGap records+2*totalWidth records+5*records.length := by
  induction records with
  | nil => rfl
  | cons record later ih =>
    simp only [totalSpan,totalGap,totalWidth,oneSpan,List.length_cons,ih]
    omega

theorem eraseFee_eq (records : List RecordSpec) :
    eraseFee records=totalGap records+8*totalWidth records+28*records.length+1 := by
  induction records with
  | nil => rfl
  | cons record later ih =>
    simp only [eraseFee,totalGap,totalWidth,List.length_cons,ih]
    omega

/-- Compiled j precedes all bank values. The structural equality length=j
describes the actual fixed number of records, not a runtime count/oracle. -/
theorem eraseBank_bounded (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive suffix : List Bool) :
    BoundedRun (s:=eraseCap j) (eraseBankMachine j) (bankEnd archive records suffix) (eraseBankPort j)
      (Tape.mk₂ archive (true::(List.replicate (totalGap records+2*totalWidth records+5*j) false++suffix)))
      (totalGap records+8*totalWidth records+28*j+1) := by
  have h := erase_records records archive suffix
  rw [hj] at h
  simpa only [eraseFee_eq,erasedBankTape,totalSpan_eq,hj] using h

/-- The SAME actual trace clears every cache record to an equal-length
FALSE span and returns to the old TRUE marker. Archive and arbitrary suffix,
including a final output stored there, are retained verbatim. -/
theorem eraseBank_contract (j : Nat) (records : List RecordSpec) (hj : records.length=j)
    (archive suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (eraseBankMachine j) ⟨0,bankEnd archive records suffix⟩ trace
        ⟨eraseBankPort j,Tape.mk₂ archive
          (true::(List.replicate (totalGap records+2*totalWidth records+5*j) false++suffix))⟩ ∧
      trace.length≤totalGap records+8*totalWidth records+28*j+1 ∧
      ∀ prefixLength chargedL, visitedSpace (eraseBankMachine j) chargedL (trace.take prefixLength) ≤
        chargedL+2*totalGap records+16*totalWidth records+56*j+3 := by
  obtain ⟨trace,hr,hl⟩ := eraseBank_bounded j records hj archive suffix
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength chargedL
  have hs := PSTRTMTrace002.visitedSpace_le (eraseBankMachine j) chargedL (trace.take prefixLength)
  have ht : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticEraseBank034
