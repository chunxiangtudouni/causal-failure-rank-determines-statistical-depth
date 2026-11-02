module
public import Common.PSTR_TM_ThresholdUnitColumnsRun_159
public import Common.PSTR_TM_Canonical_020

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitColumnsCost160
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdUnitColumnsCode156 PSTRTMThresholdUnitColumnsStep157
open PSTRTMThresholdUnitColumnsEOF158 PSTRTMThresholdUnitColumnsRun159 PSTRTMOverlap132

theorem loop_length (archive previous : List Bool) (first : Bool) (digits : List Bool) :
    (loopTrace archive previous first digits).length=
      6*digits.length^2+27*digits.length+2*previous.length+5 := by
  induction digits generalizing previous first with
  | nil => simpa only [loopTrace,List.length_nil,Nat.zero_pow (by decide : 0<2),
      Nat.mul_zero,Nat.zero_add] using eof_length archive previous first
  | cons bit later ih =>
    rw [loopTrace,glue_length,unit_length,ih]
    have he : 12*later.length+30-1=12*later.length+29 := by omega
    rw [he]
    simp only [List.length_cons]
    nlinarith

theorem unit_columns_length_le (archive digits : List Bool) :
    (loopTrace archive [] true digits).length≤64*(digits.length+1)^2 := by
  rw [loop_length]
  simp only [List.length_nil]
  nlinarith

private theorem arithmetic_space_bound (archive width time space : Nat)
    (ht : time≤64*(width+1)^2) (hs : space ≤ archive+1+2*width+2*time+1) :
    space≤archive+256*(width+1)^2 := by nlinarith

theorem unit_columns_visitedSpace_le (archive digits : List Bool) :
    visitedSpace unitMachine (archive.length+1+2*digits.length) (loopTrace archive [] true digits)≤
      archive.length+256*(digits.length+1)^2 :=
  arithmetic_space_bound _ _ _ _ (unit_columns_length_le archive digits)
    (PSTRTMTrace002.visitedSpace_le unitMachine (archive.length+1+2*digits.length) (loopTrace archive [] true digits))

theorem rawPayload_ne_nil (value : Nat) : PSTRTMNatValue017.rawPayload value≠[] := by
  intro h
  have hl : (PSTRTMNatValue017.rawPayload value).length=natBits value := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have hp : 0 < natBits value := by unfold natBits; omega
  rw [h] at hl
  simp only [List.length_nil] at hl
  omega

theorem rawPayload_one : PSTRTMNatValue017.rawPayload 1=[true] := by decide

/-- Canonical B source, original fixed214-label machine. The physical
result is EXACT resident123 input for numerator ONE, not merely a value
equation or a readout projection. Inputs and output need actual blank
right and retain all left data beyond the real false guard. -/
theorem natural_unit_columns_final_tape (archive : List Bool) (value : Nat) :
    (final archive [] true (PSTRTMNatValue017.rawPayload value)).Tape=Turing.Tape.mk₂ (false::archive)
      (PSTRTMBinaryAdd024.operandColumns
        (PSTRTMPackCode036.digitPairs (PSTRTMNatValue017.rawPayload 1) (PSTRTMNatValue017.rawPayload value))) := by
  rw [rawPayload_one]
  exact unit_columns_final_tape _ _ (rawPayload_ne_nil value)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitColumnsCost160
