module

public import Common.PSTR_SYM_DatumDispatch_033

/-! One original heterogeneous Datum, one fixed66-label real Bool program.
This is the actual body primitive needed by the outer-count scanner. It
does not supply the scanner's cursor roundtrip or whole outer EOF proof. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDatumParser

open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002
open PSTRSymbolicLocator (naturalLeft rawPayload_length)

def datumLeft (left : List Bool) : Datum → List Bool
  | .natural number => naturalLeft left number
  | .rational value => ratLeft left value

def datumTrace (left : List Bool) (value : Datum) (suffix : List Bool) : List (MachineState 65) :=
  match value with
  | .natural number => [datumState 0 left (encodeDatum (.natural number) ++ suffix)] ++
      (naturalDatumTrace left number suffix).map natCfg
  | .rational value => [datumState 0 left (encodeDatum (.rational value) ++ suffix)] ++
      (ratTrace left (sign value) (numeratorDigits value) (denominatorDigits value) suffix).map ratCfg

def datumFinal (left : List Bool) (value : Datum) (suffix : List Bool) : MachineState 65 :=
  match value with
  | .natural number => natCfg (naturalDatumFinal left number suffix)
  | .rational value => ratCfg (ratFinal left (sign value) (numeratorDigits value) (denominatorDigits value) suffix)

theorem datum_runsFrom (left : List Bool) (value : Datum) (suffix : List Bool) :
    RunsFrom datumMachine ⟨0, Tape.mk₂ left (encodeDatum value ++ suffix)⟩
      (datumTrace left value suffix) (datumFinal left value suffix) := by
  cases value with
  | natural number =>
    exact datum_nat_runsFrom left (encodeNat number ++ suffix)
      (naturalDatumTrace left number suffix) (naturalDatumFinal left number suffix)
      (naturalDatum_runsFrom left number suffix)
  | rational value =>
    exact datum_rat_runsFrom left (encodeDatum (.rational value) ++ suffix).tail
      (ratTrace left (sign value) (numeratorDigits value) (denominatorDigits value) suffix)
      (ratFinal left (sign value) (numeratorDigits value) (denominatorDigits value) suffix)
      (encodeDatum_rat_runsFrom left suffix value)

theorem datum_final_tape (left : List Bool) (value : Datum) (suffix : List Bool) :
    (datumFinal left value suffix).Tape = Tape.mk₂ (datumLeft left value) suffix := by
  cases value with
  | natural number => exact naturalDatum_final_tape left number suffix
  | rational value => exact rat_final_tape left (sign value) (numeratorDigits value) (denominatorDigits value) suffix

theorem datum_time_le (left : List Bool) (value : Datum) (suffix : List Bool) :
    (datumTrace left value suffix).length ≤ 128 * ((encodeDatum value).length + 1)^2 := by
  cases value with
  | natural number =>
    have clock := naturalDatum_time_le left number suffix
    simp only [datumTrace, List.length_append, List.length_cons, List.length_nil,
      List.length_map, PSTRTMLength004.encodeDatum_natural_length]
    calc
      _ ≤ 1 + 17 * (natBits number + 1)^2 := Nat.add_le_add_left clock 1
      _ ≤ 128 * (2 * natBits number + 2 + 1)^2 := by
        nlinarith [Nat.zero_le (natBits number), Nat.zero_le ((natBits number)^2)]
  | rational value =>
    simp only [datumTrace, List.length_append, List.length_cons, List.length_nil, List.length_map,
      ratTrace_length, numeratorDigits, denominatorDigits, rawPayload_length,
      PSTRTMLength004.encodeDatum_rational_length]
    nlinarith [Nat.zero_le ((natBits value.num.natAbs)^2), Nat.zero_le ((natBits value.den)^2),
      Nat.zero_le (natBits value.num.natAbs * natBits value.den)]

theorem datum_prefix_space (left : List Bool) (value : Datum) (suffix : List Bool)
    (inputLength clock : Nat) :
    visitedSpace datumMachine inputLength ((datumTrace left value suffix).take clock) ≤
      inputLength + 256 * ((encodeDatum value).length + 1)^2 + 1 := by
  have time := datum_time_le left value suffix
  have cells := PSTRTMTrace002.visitedSpace_le datumMachine inputLength
    ((datumTrace left value suffix).take clock)
  have length : ((datumTrace left value suffix).take clock).length ≤ (datumTrace left value suffix).length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicDatumParser
