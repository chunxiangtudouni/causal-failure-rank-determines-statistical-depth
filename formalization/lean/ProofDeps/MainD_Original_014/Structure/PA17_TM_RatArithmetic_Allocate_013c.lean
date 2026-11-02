module
public import Structure.PA17_TM_RatArithmetic_Allocate_013b
public import Common.PSTR_TM_PackFinish_039

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013

open Turing

/-- A genuinely blank infinite tail already contains the cells that the
constant finite-code chunk will actually visit and clear. -/
theorem gap_blank_entry (k : Nat) (left : List Bool) :
    Tape.mk₂ left (true :: (List.replicate k false ++ [])) = Tape.mk₂ left [true] := by
  simp only [List.append_nil]
  change Tape.mk' (ListBlank.mk left) (ListBlank.mk ([true] ++ List.replicate k false)) =
    Tape.mk' (ListBlank.mk left) (ListBlank.mk [true])
  rw [PSTRTMPackFinish039.blank_false_suffix]

/-- No supplied padding is required for the original standalone blank tail.
The very same gapMachine still performs all 3*k actual transitions. -/
theorem gap_runsFrom_blank (k : Nat) (left : List Bool) :
    PSTRTMSeq005.RunsFrom (gapMachine k) ⟨0,Tape.mk₂ left [true]⟩
      (gapTrace k 0 k (by omega) left [])
      (gapState k (3*k) (by omega) (List.replicate k false ++ left) [true]) := by
  simpa only [gap_blank_entry] using gap_runsFrom k left []

theorem gap_blank_contract (k : Nat) (left : List Bool) :
    ∃ trace,
      PSTRTMSeq005.RunsFrom (gapMachine k) ⟨0,Tape.mk₂ left [true]⟩ trace
        (gapState k (3*k) (by omega) (List.replicate k false ++ left) [true]) ∧
      trace.length = 3*k+1 ∧
      ∀ prefixLength inputLength,
        visitedSpace (gapMachine k) inputLength (trace.take prefixLength) ≤ inputLength+6*k+3 := by
  exact ⟨gapTrace k 0 k (by omega) left [],gap_runsFrom_blank k left,
    gap_length k 0 k (by omega) left [],gap_prefix_space k left []⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013
