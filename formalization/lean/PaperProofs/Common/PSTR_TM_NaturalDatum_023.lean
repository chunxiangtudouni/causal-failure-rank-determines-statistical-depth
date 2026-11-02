module
public import PaperProofs.Common.PSTR_TM_Prepend_022

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNaturalDatum023
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMNativeIncrement021 PSTRTMNatValue017 PSTRTMCanonical020 PSTRTMPrepend022

/-- Exposed specialized types prevent semireducible prefixStates from
entering later List typeclass/rewrite matching. These are exact aliases. -/
def tagTrace (input : List Bool) : List (MachineState 3) := prefixTrace [false] input
def tagFinal (input : List Bool) : MachineState 3 := prefixFinal [false] input

theorem tag_length (input : List Bool) : (tagTrace input).length = 4 :=
  prefix_length [false] input

theorem tag_runs (input : List Bool) :
    Runs naturalTagMachine input (tagTrace input) (tagFinal input) := prefix_runs [false] input

theorem tag_final_tape (input : List Bool) :
    (tagFinal input).Tape = Turing.Tape.mk₁ (false :: input) := prefix_final_tape [false] input

/-- Uniform56-label Bool program: the complete raw arithmetic computation,
then the actual original natural Datum tag. No encoded output is supplied. -/
def naturalDatumMachine : Machine 55 :=
  PSTRTMSeq005.seqMachine nativeIncrementMachine naturalTagMachine

def datumTrace (digits : List Bool) : List (MachineState 55) :=
  (nativeTrace digits).map (PSTRTMSeq005.leftCfg (b := 3)) ++
    (tagTrace (PSTRTMUnblockTrace019.rawWord (PSTRTMIncrement009.bumpDigits digits))).map
      (PSTRTMSeq005.rightCfg (a := 51) (b := 3))

def datumFinal (digits : List Bool) : MachineState 55 :=
  PSTRTMSeq005.rightCfg (a := 51) (b := 3)
    (tagFinal (PSTRTMUnblockTrace019.rawWord (PSTRTMIncrement009.bumpDigits digits)))

theorem native_final_tape (digits : List Bool) :
    (nativeFinal digits).Tape =
      Turing.Tape.mk₁ (PSTRTMUnblockTrace019.rawWord (PSTRTMIncrement009.bumpDigits digits)) := by
  simp only [nativeFinal, PSTRTMSeq005.rightCfg, PSTRTMUnblock018.state,
    Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]

theorem datum_runs (digits : List Bool) :
    Runs naturalDatumMachine (PSTRTMUnblockTrace019.rawWord digits) (datumTrace digits) (datumFinal digits) := by
  apply PSTRTMSeq005.seq_runs nativeIncrementMachine naturalTagMachine (PSTRTMUnblockTrace019.rawWord digits)
    (nativeFinal digits) (tagFinal (PSTRTMUnblockTrace019.rawWord (PSTRTMIncrement009.bumpDigits digits)))
    (nativeTrace digits) (tagTrace (PSTRTMUnblockTrace019.rawWord (PSTRTMIncrement009.bumpDigits digits)))
  · exact native_runs digits
  · have h := tag_runs (PSTRTMUnblockTrace019.rawWord (PSTRTMIncrement009.bumpDigits digits))
    refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1⟩
    rw [native_final_tape]
    exact h.1

theorem datum_length_le (digits : List Bool) :
    (datumTrace digits).length ≤ 2 * digits.length^2 + 32 * digits.length + 33 := by
  have h := native_length_le digits
  rw [datumTrace, PSTRTMSeq005.seq_trace_length (a := 51) (b := 3)]
  have htag : (tagTrace
      (PSTRTMUnblockTrace019.rawWord (PSTRTMIncrement009.bumpDigits digits))).length = 4 := by
    exact tag_length _
  rw [htag]
  omega

theorem datum_computes_digits (digits : List Bool) :
    computes naturalDatumMachine (PSTRTMUnblockTrace019.rawWord digits)
      (false :: PSTRTMUnblockTrace019.rawWord (PSTRTMIncrement009.bumpDigits digits))
      (1024 * (digits.length+1)^2) (1024 * (digits.length+1)^2) := by
  refine ⟨datumTrace digits, datumFinal digits, datum_runs digits, ?_, ?_, ?_⟩
  · simp only [datumFinal, PSTRTMSeq005.rightCfg]
    rw [tag_final_tape]
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
  · have ht := datum_length_le digits
    nlinarith
  · have hs := PSTRTMTrace002.visitedSpace_le naturalDatumMachine
      (PSTRTMUnblockTrace019.rawWord digits).length (datumTrace digits)
    have ht := datum_length_le digits
    simp only [PSTRTMUnblockTrace019.rawWord, List.length_append,
      List.length_replicate, List.length_cons] at hs ⊢
    nlinarith

/-- Full actual arithmetic PLUS original Datum serialization; input is the
original raw Nat, output is EXACT original encodeDatum(.natural(value+1)). -/
theorem encodeNat_increment_datum_computes (value : Nat) :
    computes naturalDatumMachine (encodeNat value) (encodeDatum (.natural (value+1)))
      (1024 * (natBits value+1)^2) (1024 * (natBits value+1)^2) := by
  have h := datum_computes_digits (rawPayload value)
  rw [rawWord_bump] at h
  simpa [PSTRTMUnblockTrace019.rawWord, rawPayload, encodeNat, encodeDatum] using h

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNaturalDatum023
