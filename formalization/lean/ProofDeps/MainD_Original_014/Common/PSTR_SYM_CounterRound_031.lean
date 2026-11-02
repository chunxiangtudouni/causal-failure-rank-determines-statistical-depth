module

public import Common.PSTR_SYM_CounterEntry_030

/-! Actual fixed17-label composition of the existing borrow and zero-test.
It consumes NO original Datum. The eventual scanner must call it after a
real field parse; zero here is not by itself a global EOF certificate. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCounter

open Turing PSTRTMSeq005 PSTRTMIncrement009
open PSTRTMThresholdCountdownCode164 PSTRTMThresholdCountdownRun166
open PSTRTMThresholdDepthZeroCode167 PSTRTMThresholdDepthZeroRun168

def counterRoundMachine : Machine 16 := seqMachine countdownMachine zeroMachine

def counterRoundTrace (archive digits suffix : List Bool) : List (MachineState 16) :=
  (borrowTrace archive 0 digits (false :: false :: suffix)).map (leftCfg (b := 7)) ++
    (zeroTrace archive [] false (predDigits digits) suffix).map (rightCfg (a := 8))

def counterRoundFinal (archive digits suffix : List Bool) : MachineState 16 :=
  rightCfg (a := 8) (PSTRTMThresholdDepthZeroRun168.final archive [] false (predDigits digits) suffix)

theorem counterRound_runsFrom (archive digits suffix : List Bool) (positive : true ∈ digits) :
    RunsFrom counterRoundMachine ⟨0, Tape.mk₂ (false :: archive)
      (blocks digits ++ false :: false :: suffix)⟩
      (counterRoundTrace archive digits suffix) (counterRoundFinal archive digits suffix) := by
  apply seq_runsFrom countdownMachine zeroMachine
    ⟨0, Tape.mk₂ (false :: archive) (blocks digits ++ false :: false :: suffix)⟩
    (PSTRTMThresholdCountdownCode164.state 8 (false :: archive)
      (blocks (predDigits digits) ++ false :: false :: suffix))
    (PSTRTMThresholdDepthZeroRun168.final archive [] false (predDigits digits) suffix)
    (borrowTrace archive 0 digits (false :: false :: suffix))
    (zeroTrace archive [] false (predDigits digits) suffix)
  · exact countdown_runsFrom archive digits (false :: false :: suffix) positive
  · exact zero_runsFrom archive (predDigits digits) suffix

theorem counterRound_final_tape (archive digits suffix : List Bool) :
    (counterRoundFinal archive digits suffix).Tape =
      Tape.mk₂ (PSTRTMRawNat010.leftBlocks (predDigits digits).reverse ++ false :: archive)
        (false :: false :: suffix) := by
  simp only [counterRoundFinal, rightCfg, PSTRTMThresholdDepthZeroRun168.final,
    PSTRTMThresholdDepthZeroCode167.state, contextLeft, List.append_nil]

/-- The real finite return label, rather than an externally supplied flag. -/
theorem counterRound_zero_port (archive digits suffix : List Bool) (positive : true ∈ digits) :
    (counterRoundFinal archive digits suffix).q.val = 15 ↔ valueDigits digits = 1 := by
  have observed := countdown_seen_false_iff digits positive
  cases seenEq : seen false (predDigits digits) <;>
    simp_all [counterRoundFinal, rightCfg, rightLabel, PSTRTMThresholdDepthZeroRun168.final,
      PSTRTMThresholdDepthZeroCode167.state, haltLabel]

theorem counterRound_value (digits : List Bool) (positive : true ∈ digits) :
    valueDigits (predDigits digits) + 1 = valueDigits digits := pred_value digits positive

theorem counterRound_width (digits : List Bool) :
    (predDigits digits).length = digits.length := pred_length digits

theorem counterRound_time_le (archive digits suffix : List Bool) (positive : true ∈ digits) :
    (counterRoundTrace archive digits suffix).length ≤ 8 * (digits.length + 1) := by
  have borrow := borrow_length_le archive 0 digits (false :: false :: suffix) positive
  simp only [counterRoundTrace, List.length_append, List.length_map, zero_length, pred_length]
  omega

theorem counterRound_prefix_space (archive digits suffix : List Bool) (positive : true ∈ digits)
    (inputLength clock : Nat) :
    visitedSpace counterRoundMachine inputLength ((counterRoundTrace archive digits suffix).take clock) ≤
      inputLength + 16 * (digits.length + 1) + 1 := by
  have time := counterRound_time_le archive digits suffix positive
  have cells := PSTRTMTrace002.visitedSpace_le counterRoundMachine inputLength
    ((counterRoundTrace archive digits suffix).take clock)
  have length : ((counterRoundTrace archive digits suffix).take clock).length ≤
      (counterRoundTrace archive digits suffix).length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicCounter
