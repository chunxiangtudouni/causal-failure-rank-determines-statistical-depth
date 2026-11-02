module
public import Structure.PA17_TM_Division_Codec_003g

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
open PaperProofs.Common.Native.RationalControllerComputation

/-- The common actual loop-exit tape, headed at the resident's first A
cell. This is a tape description, not an original input qualification. -/
def residentTape (archive resident : List (Bool × Bool)) : Turing.Tape Bool :=
  Turing.Tape.mk₂
    (false :: false :: false :: (PSTRTMBinaryAdd024.operandColumns archive).reverse)
    (PSTRTMBinaryAdd024.operandColumns resident ++ [false,false])

private theorem residentLeft_guard (archive : List (Bool × Bool)) :
    Turing.ListBlank.mk
      (false :: false :: false :: ((PSTRTMBinaryAdd024.operandColumns archive).reverse ++ [false])) =
    Turing.ListBlank.mk
      (false :: false :: false :: (PSTRTMBinaryAdd024.operandColumns archive).reverse) := by
  exact PSTRTMRawNat010.blank_append_false
    (false :: false :: false :: (PSTRTMBinaryAdd024.operandColumns archive).reverse)

private theorem residentRight_own00 (resident : List (Bool × Bool)) :
    Turing.ListBlank.mk (PSTRTMBinaryAdd024.operandColumns resident ++ [false,false]) =
      Turing.ListBlank.mk (PSTRTMBinaryAdd024.operandColumns resident) :=
  PSTRTMPackFinish039.blank_false_suffix _ 2

theorem quotientTail_initial_eq (archive resident : List (Bool × Bool)) :
    quotientTailInitial archive resident =
      (⟨0, residentTape archive resident⟩ : MachineState 140) := by
  simp only [quotientTailInitial, scanEraseInitial, archiveContext, residentTape,
    Turing.Tape.mk₂]
  rw [residentLeft_guard]

theorem remainderTail_initial_eq (archive resident : List (Bool × Bool)) :
    remainderTailInitial (PSTRTMPackLoop043.pairedDigits archive) resident =
      (⟨0, residentTape archive resident⟩ : MachineState 117) := by
  have hl : PSTRTMRawNat010.leftBlocks (PSTRTMPackLoop043.pairedDigits archive).reverse =
      (PSTRTMBinaryAdd024.operandColumns archive).reverse := by
    rw [← PSTRTMCompareRun059.leftColumns_reverse, leftColumns_reverse_columns]
  simp only [remainderTailInitial, remainderProjectInitial, residentTape, hl, Turing.Tape.mk₂]
  rw [residentLeft_guard, residentRight_own00]

theorem quotientTail_from_resident (archive resident : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom quotientTailMachine
      ⟨0, residentTape archive resident⟩
      (quotientTailTrace archive resident) (quotientTailFinal archive) := by
  have hr := quotientTail_runsFrom archive resident
  rw [quotientTail_initial_eq] at hr
  exact hr

theorem remainderTail_from_resident (archive resident : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom remainderTailMachine
      ⟨0, residentTape archive resident⟩
      (remainderTailTrace (PSTRTMPackLoop043.pairedDigits archive) resident)
      (remainderTailFinal resident) := by
  have hr := remainderTail_runsFrom (PSTRTMPackLoop043.pairedDigits archive) resident
  rw [remainderTail_initial_eq] at hr
  exact hr

/-- Both fixed programs start on exactly the same physical loop result.
Every transfer, cleanup, output write, canonical-zero case and final HALT
is part of its exhibited genuine trace. Quotient/remainder arithmetic is
supplied by the shared loop's actual first-track value theorems. -/
theorem both_postludes (archive resident : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom quotientTailMachine
      ⟨0, residentTape archive resident⟩
      (quotientTailTrace archive resident) (quotientTailFinal archive) ∧
    PSTRTMSeq005.RunsFrom remainderTailMachine
      ⟨0, residentTape archive resident⟩
      (remainderTailTrace (PSTRTMPackLoop043.pairedDigits archive) resident) (remainderTailFinal resident) ∧
    (quotientTailFinal archive).Tape =
      Turing.Tape.mk₁ (encodeNat (PSTRTMBinaryAdd024.firstValue archive)) ∧
    (remainderTailFinal resident).Tape =
      Turing.Tape.mk₁ (encodeNat (PSTRTMBinaryAdd024.firstValue resident)) :=
  ⟨quotientTail_from_resident archive resident, remainderTail_from_resident archive resident,
    quotientTail_final_tape archive, remainderTail_final_tape resident⟩

theorem remainder_from_resident_length_le (archive resident : List (Bool × Bool)) :
    (remainderTailTrace (PSTRTMPackLoop043.pairedDigits archive) resident).length ≤
      12 * archive.length + 9 * resident.length + 19 + 128 * (resident.length + 1)^2 := by
  have ht := remainderTailTrace_length_le (PSTRTMPackLoop043.pairedDigits archive) resident
  rw [PSTRTMCompareRun059.pairedDigits_length] at ht
  omega

theorem remainder_from_resident_visitedSpace_le (inputLength : Nat)
    (archive resident : List (Bool × Bool)) :
    visitedSpace remainderTailMachine inputLength
      (remainderTailTrace (PSTRTMPackLoop043.pairedDigits archive) resident) ≤
      inputLength + 24 * archive.length + 18 * resident.length + 39 +
        256 * (resident.length + 1)^2 := by
  have hs := remainderTailTrace_visitedSpace_le inputLength
    (PSTRTMPackLoop043.pairedDigits archive) resident
  rw [PSTRTMCompareRun059.pairedDigits_length] at hs
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
