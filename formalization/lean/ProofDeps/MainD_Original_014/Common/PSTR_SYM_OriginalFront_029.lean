module

public import Common.PSTR_SYM_RestoredBranch_028
public import Common.PSTR_SYM_OriginalPriorRun_013

/-! ONE fixed338-label program on the full original input domain. A real
input-bit branch selects the original zero-output program or positive prior
stager, after genuinely restoring the original count. The positive branch
is staging ONLY; full SymbolicCompilationClaims is still unproved. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicFront

open PaperProofs.Common Turing PSTRTMSeq005 PA17TMRatArithmeticParse002

def originalRemainder {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    List Datum := (rawInstance input ++ rawSet available).tail

theorem originalData_cons {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    rawInstance input ++ rawSet available = .natural I.stageCount :: originalRemainder input available := by
  rfl

theorem original_front_bits {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    CompactPrice.symbolicInput input available =
      encodeNat (rawInstance input ++ rawSet available).length ++ encodeDatum (.natural I.stageCount) ++
        ((originalRemainder input available).flatMap encodeDatum ++ [true]) := by
  unfold CompactPrice.symbolicInput encode
  have fields := congrArg (fun data : List Datum => data.flatMap encodeDatum)
    (originalData_cons input available)
  rw [fields]
  simp only [List.flatMap_cons, List.append_assoc]

theorem original_count_room {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    natBits (rawInstance input ++ rawSet available).length + 1 ≤
      (CompactPrice.symbolicInput input available).length + 1 := by
  rw [original_front_bits]
  simp only [List.length_append, PSTRTMLength004.encodeNat_length]
  omega

theorem original_runsFrom {states : Nat} (machine : Machine states) (input : List Bool)
    (trace : List (MachineState states)) (final : MachineState states)
    (actual : Runs machine input trace final) :
    RunsFrom machine ⟨0, Tape.mk₁ input⟩ trace final := by
  refine ⟨?_, actual.2.1, actual.2.2.1, actual.2.2.2.1⟩
  simpa only [TM0.init, Fin.default_eq_zero] using actual.1

theorem original_front_runs {states : Nat} (machine : Machine states) (input : List Bool)
    (trace : List (MachineState states)) (final : MachineState states)
    (actual : RunsFrom machine ⟨0, Tape.mk₁ input⟩ trace final) :
    Runs machine input trace final := by
  apply PSTRTMTrace002.runs_of_chain
  · simpa only [TM0.init, Fin.default_eq_zero] using actual.1
  · exact actual.2.1
  · exact actual.2.2.1
  · exact actual.2.2.2

/-- The same fixed full-domain code really takes its zero branch. No host
choice of a different machine, cursor reset or extra input field is used. -/
theorem original_front_zero_computes {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (zero : I.stageCount = 0) :
    computes symbolicFrontMachine (CompactPrice.symbolicInput input available)
      (CompactPrice.symbolicOutput input available)
      (32768 * ((CompactPrice.symbolicInput input available).length + 1)^2)
      (32768 * ((CompactPrice.symbolicInput input available).length + 1)^2) := by
  obtain ⟨calleeTrace, calleeFinal, calleeRun, output, calleeTime, _calleeSpace⟩ :=
    PSTRSymbolicZeroTail.original_zero_computes input available zero
  change @List.length (MachineState 173) calleeTrace ≤
    4096 * ((CompactPrice.symbolicInput input available).length + 1)^2 at calleeTime
  have bits := original_front_bits input available
  rw [zero] at bits
  have callee := original_runsFrom _ _ _ _ calleeRun
  rw [bits] at callee
  obtain ⟨trace, final, run, tape, time⟩ := front_zero_runsFrom
    (rawInstance input ++ rawSet available).length
    ((originalRemainder input available).flatMap encodeDatum ++ [true]) calleeTrace calleeFinal callee
  rw [← bits] at run
  have actual := original_front_runs symbolicFrontMachine _ trace final run
  have width := original_count_room input available
  have square := Nat.pow_le_pow_left width 2
  have room := Nat.mul_le_mul_left 48 square
  have squarePositive : 1 ≤ ((CompactPrice.symbolicInput input available).length + 1)^2 := by nlinarith
  have total : trace.length ≤ 8192 * ((CompactPrice.symbolicInput input available).length + 1)^2 := by
    omega
  have cells := PSTRTMTrace002.visitedSpace_le symbolicFrontMachine
    (CompactPrice.symbolicInput input available).length trace
  have inputRoom : (CompactPrice.symbolicInput input available).length + 1 ≤
      ((CompactPrice.symbolicInput input available).length + 1)^2 := by nlinarith
  refine ⟨trace, final, actual, ?_, ?_, ?_⟩
  · rw [tape]
    exact output
  · omega
  · omega

/-- Positive inputs reach the actual prior stager using the SAME code as
the zero case. The entire original remaining suffix is preserved. This is
not the missing positive AST/serializer, and is not a full compiler. -/
theorem original_front_positive_prior {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (positive : 0 < I.stageCount) :
    ∃ (numbers : List Nat) (remaining : List Datum)
      (trace : List (MachineState frontCap)) (final : MachineState frontCap),
      rawInstance input ++ rawSet available = numbers.map Datum.natural ++
        .rational (input.experiment (PSTRSymbolicLocator.firstStage positive)).priorOne :: remaining ∧
      Runs symbolicFrontMachine (CompactPrice.symbolicInput input available) trace final ∧
      final.Tape = Tape.mk₂
        (ratLeft (PSTRSymbolicLocator.firstRatArchive [] (rawInstance input ++ rawSet available).length numbers)
          (input.experiment (PSTRSymbolicLocator.firstStage positive)).priorOne)
        (remaining.flatMap encodeDatum ++ [true]) ∧
      trace.length ≤ 2048 * ((CompactPrice.symbolicInput input available).length + 1)^2 ∧
      visitedSpace symbolicFrontMachine (CompactPrice.symbolicInput input available).length trace ≤
        2048 * ((CompactPrice.symbolicInput input available).length + 1)^2 := by
  obtain ⟨numbers, remaining, calleeTrace, calleeFinal, data, calleeRun, tape, calleeTime, _calleeSpace⟩ :=
    PSTRSymbolicLocator.original_positive_prior input available positive
  have bits := original_front_bits input available
  have callee := original_runsFrom _ _ _ _ calleeRun
  rw [bits] at callee
  obtain ⟨trace, final, run, sameTape, time⟩ := front_positive_runsFrom
    (rawInstance input ++ rawSet available).length I.stageCount
    ((originalRemainder input available).flatMap encodeDatum ++ [true]) positive calleeTrace calleeFinal callee
  rw [← bits] at run
  have actual := original_front_runs symbolicFrontMachine _ trace final run
  have width := original_count_room input available
  have square := Nat.pow_le_pow_left width 2
  have room := Nat.mul_le_mul_left 48 square
  have squarePositive : 1 ≤ ((CompactPrice.symbolicInput input available).length + 1)^2 := by nlinarith
  have total : trace.length ≤ 512 * ((CompactPrice.symbolicInput input available).length + 1)^2 := by omega
  have cells := PSTRTMTrace002.visitedSpace_le symbolicFrontMachine
    (CompactPrice.symbolicInput input available).length trace
  have inputRoom : (CompactPrice.symbolicInput input available).length + 1 ≤
      ((CompactPrice.symbolicInput input available).length + 1)^2 := by nlinarith
  refine ⟨numbers, remaining, trace, final, data, actual, sameTape.trans tape, ?_, ?_⟩ <;> omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicFront
