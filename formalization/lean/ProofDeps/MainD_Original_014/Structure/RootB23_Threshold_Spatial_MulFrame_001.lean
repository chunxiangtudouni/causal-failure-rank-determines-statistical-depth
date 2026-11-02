module
public import Structure.PA17_TM_RatArithmetic_MulSuffix_063c
public import Structure.PA17_TM_RatArithmetic_FrameBudget_008a

/-! Internal SAME-code RAW multiplication consumer. The displayed window
must be produced by an actual caller. This is neither a window allocator nor
the original five-output THRESHOLD theorem. The machine has no width, room,
answer or spare parameter. All original Rat signs and zero are covered. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23.Threshold.Spatial

open Turing
open PA17TMRatArithmeticMulSuffix063 PA17TMRatArithmeticMulController057
open PA17TMRatArithmeticFrame005 PA17TMRatArithmeticFrameBudget008

def rawInputLength (x y : Rat) : Nat := (encode [.rational x, .rational y]).length

def rawTime (x y : Rat) : Nat := mulTimeCoefficient * originalPower x y

/-- A proof index for physically present cells, not a machine parameter. -/
def rawWindow (x y : Rat) (spare : Nat) : Nat :=
  rawTime x y + 2 * rawInputLength x y + spare + 2

theorem raw_product_length_le (x y : Rat) :
    (encode [.rational (x * y)]).length ≤ 2 * rawInputLength x y := by
  have fields := PA17TMRatArithmeticMulFields048.pipeline_fields x y
  have bits := PA17TMRatArithmeticMulFields048.normalized_bits x y
  have numerator : natBits (x * y).num.natAbs ≤ PA17TMRatArithmeticParse002.fieldWidth x y := by
    rw [← fields.1]
    exact bits.1
  have denominator : natBits (x * y).den ≤ PA17TMRatArithmeticParse002.fieldWidth x y := by
    rw [← fields.2.1]
    exact bits.2
  have input := PA17TMRatArithmeticParse002.pair_length x y
  unfold PA17TMRatArithmeticParse002.fieldWidth at numerator denominator
  have oneBits : natBits 1 = 1 := by decide
  simp only [PSTRTMLength004.encode_length, List.length_singleton,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    PSTRTMLength004.datumBits, oneBits, Nat.add_zero]
  unfold rawInputLength
  omega

theorem raw_window_original_bound (x y : Rat) (spare : Nat) :
    rawWindow x y spare ≤
      (mulTimeCoefficient + spare + 2) * (rawInputLength x y + 1) ^ 4 := by
  let i := rawInputLength x y
  have linear : i + 1 ≤ (i + 1) ^ 4 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by omega : 1 ≤ i + 1) (by decide : (1 : Nat) ≤ 4)
  have margin : 2 * i + spare + 2 ≤ (spare + 2) * (i + 1) := by
    nlinarith [Nat.zero_le (spare * i)]
  calc
    rawWindow x y spare = rawTime x y + (2 * i + spare + 2) := by
      unfold rawWindow i
      omega
    _ ≤ rawTime x y + (spare + 2) * (i + 1) := Nat.add_le_add_left margin _
    _ ≤ rawTime x y + (spare + 2) * (i + 1) ^ 4 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ linear) _
    _ = (mulTimeCoefficient + spare + 2) * (rawInputLength x y + 1) ^ 4 := by
      unfold rawTime originalPower i rawInputLength
      ring

/-- Exact output and head after unchanged RAW64 code, including all old
allocation, arithmetic, canonicalization and true HALT. Outside data remains
at its original physical boundary. Room hypotheses are internal producer
obligations; no original THRESHOLD caller may assume them for free. -/
theorem raw_mul_framed (x y : Rat) (archive suffix : List Bool) (spare : Nat)
    (left right : Nat) (leftRoom : rawWindow x y spare ≤ left)
    (rightRoom : rawWindow x y spare ≤ right) :
    ∃ (finalLeft finalRight : Nat) (trace : List (MachineState controllerCap))
      (final : MachineState controllerCap),
      PSTRTMSeq005.RunsFrom mulMachine
        ⟨0, Tape.mk₂ (List.replicate left false ++ archive)
          (encode [.rational x, .rational y] ++
            List.replicate (right + 1 - rawInputLength x y) false ++ suffix)⟩
        trace final ∧
      final.Tape = Tape.mk₂ (List.replicate finalLeft false ++ archive)
        (encode [.rational (x * y)] ++
          List.replicate (finalRight + 1 - (encode [.rational (x * y)]).length) false ++ suffix) ∧
      spare ≤ finalLeft ∧
      spare ≤ finalRight + 1 - (encode [.rational (x * y)]).length ∧
      finalLeft + finalRight = left + right ∧
      trace.length ≤ rawTime x y ∧
      ∀ prefixLength inputLength,
        visitedSpace mulMachine inputLength (trace.take prefixLength) ≤
          inputLength + 2 * rawTime x y + 1 := by
  obtain ⟨oldTrace, oldFinal, oldRun, wholeFinal, oldTime⟩ := original_mul_runs x y
  have runFrom : PSTRTMSeq005.RunsFrom mulMachine
      (TM0.init (encode [.rational x, .rational y])) oldTrace oldFinal :=
    ⟨oldRun.1, oldRun.2.1, oldRun.2.2.1, oldRun.2.2.2.1⟩
  change oldTrace.length ≤ rawTime x y at oldTime
  have leftBound : oldTrace.length ≤ left := by unfold rawWindow at leftRoom; omega
  have rightBound : oldTrace.length ≤ right := by unfold rawWindow at rightRoom; omega
  obtain ⟨finalLeft, finalRight, trace, run, length, _sameDisplacements,
      sum, leftSpent, rightSpent⟩ :=
    frame_runsFrom_budget mulMachine archive suffix oldTrace
      (TM0.init (encode [.rational x, .rational y])) oldFinal left right
      runFrom leftBound rightBound
  have inputFits : (encode [.rational x, .rational y]).length ≤ right + 1 := by
    change rawInputLength x y ≤ right + 1
    unfold rawWindow at rightRoom
    omega
  have productLength := raw_product_length_le x y
  have outputFits : (encode [.rational (x * y)]).length ≤ finalRight + 1 := by
    unfold rawWindow at rightRoom
    omega
  have initialTape : frameCfg left right archive suffix
      (TM0.init (encode [.rational x, .rational y])) =
      (⟨0, Tape.mk₂ (List.replicate left false ++ archive)
        (encode [.rational x, .rational y] ++
          List.replicate (right + 1 - rawInputLength x y) false ++ suffix)⟩ :
        MachineState controllerCap) := by
    unfold frameCfg TM0.init
    rw [frameTape_mk₁ _ _ _ _ _ inputFits]
    rfl
  rw [initialTape] at run
  refine ⟨finalLeft, finalRight, trace, frameCfg finalLeft finalRight archive suffix oldFinal,
    run, ?_, ?_, ?_, sum, ?_, ?_⟩
  · change frameTape oldFinal.Tape finalLeft finalRight archive suffix = _
    rw [wholeFinal, frameTape_mk₁ _ _ _ _ _ outputFits]
  · unfold rawWindow at leftRoom
    omega
  · unfold rawWindow at rightRoom
    omega
  · omega
  · intro prefixLength inputLength
    have space := PSTRTMTrace002.visitedSpace_le mulMachine inputLength (trace.take prefixLength)
    have takeBound : (trace.take prefixLength).length ≤ trace.length := by
      rw [List.length_take]
      exact Nat.min_le_right _ _
    omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23.Threshold.Spatial
