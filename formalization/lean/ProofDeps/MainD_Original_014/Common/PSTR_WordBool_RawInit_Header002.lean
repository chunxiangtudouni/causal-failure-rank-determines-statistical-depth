module

public import Common.PSTR_WordBool_RawInit_Shape001
public import Structure.PA17_TM_RatArithmetic_Parse_002c

/-! Actual outer-count entry for every original RCC datum list, including
empty data and either first tag. The untouched suffix is the exact original
Datum bytes and true footer. This is a front segment, not the full33-row
initializer and not a supplied count/length certificate. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002

abbrev headerMachine : Machine 17 := streamMachine

def rawTail (data : List Datum) : List Bool := data.flatMap encodeDatum ++ [true]

theorem actual_count_header (data : List Datum) :
    ∃ (trace : List (MachineState 17)) (final : MachineState 17),
      Runs headerMachine (encode data) trace final ∧
      final.q = 17 ∧
      final.Tape = Tape.mk₂
        (false :: PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload data.length).reverse)
        (rawTail data) ∧
      PSTRTMIncrement009.valueDigits (PSTRTMNatValue017.rawPayload data.length) = data.length ∧
      trace.length ≤ 64 * ((encode data).length + 1)^2 ∧
      ∀ clock, visitedSpace headerMachine (encode data).length (trace.take clock) ≤
        64 * ((encode data).length + 1)^2 := by
  let suffix := rawTail data
  let digits := PSTRTMNatValue017.rawPayload data.length
  let trace := streamTrace [] [] digits suffix
  let final := streamFinal [] digits suffix
  have inputEq : encode data = encodeNat data.length ++ suffix := by
    simp only [encode, suffix, rawTail, List.append_assoc]
  have actual := encodeNat_stream_runsFrom [] suffix data.length
  have first : trace.head? = some (TM0.init (encode data)) := by
    change trace.head? = some (streamState 0 [] (encode data))
    rw [inputEq]
    exact actual.1
  have runs : Runs headerMachine (encode data) trace final :=
    PSTRTMTrace002.runs_of_chain headerMachine (encode data) trace final
      first actual.2.1 actual.2.2.1 actual.2.2.2
  have width : digits.length = natBits data.length := by
    simp only [digits, PSTRTMNatValue017.rawPayload, List.length_ofFn]
  have inputRoom : digits.length + 1 ≤ (encode data).length + 1 := by
    rw [width, PSTRTMLength004.encode_length]
    omega
  have parseTime : trace.length ≤ 16 * (digits.length + 1)^2 :=
    stream_length_le [] digits suffix
  have time : trace.length ≤ 16 * ((encode data).length + 1)^2 :=
    parseTime.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left inputRoom 2))
  refine ⟨trace, final, runs, rfl, ?_,
    PSTRTMNatValue017.valueDigits_rawPayload data.length, ?_, ?_⟩
  · simpa only [final, suffix, streamFinal, List.append_nil] using
      stream_final_tape [] digits suffix
  · omega
  · intro clock
    have space := PSTRTMTrace002.visitedSpace_le headerMachine (encode data).length (trace.take clock)
    have short : (trace.take clock).length ≤ trace.length := by
      simp only [List.length_take]
      exact Nat.min_le_right _ _
    have room : (encode data).length + 1 ≤ ((encode data).length + 1)^2 := by
      nlinarith
    omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit
