module

public import Structure.RootB23_Threshold_Window_TotalWidth_013
public import Structure.RootB23_Threshold_Window_CounterCopies_010

/-! A complete real caller for the closed quartic allocator: one destination
field is produced by appending the four source fields, actually normalized,
copied three more times, and passed to the real depth-four program. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PhysicalReserve
open Turing PSTRTMSeq005
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031

def fourSourceCounterMachine : Machine 4504 :=
  seqMachine TotalWidth.totalWidthMachine prepareFourCounterMachine

def preservedArchive (archive nx dx ny dy : List Bool) : List Bool :=
  true :: false :: TotalWidth.bankLeft archive nx dx ny dy

theorem fourSourceCounter_bounded (archive nx dx ny dy : List Bool) :
    BoundedRun fourSourceCounterMachine
      (Tape.mk₂ (false :: archive)
        (fieldWord (nxContext dx ny dy) (false :: nx) (workSuffix 0 []))) 4504
      (Tape.mk₂ (false :: preservedArchive archive nx dx ny dy)
        (powerWord (TotalWidth.width nx dx ny dy) 4 0))
      (512 * (TotalWidth.width nx dx ny dy + 1) ^ 2 +
        12 * TotalWidth.width nx dx ny dy ^ 2 + 82 * TotalWidth.width nx dx ny dy + 105) := by
  have source := (TotalWidth.totalWidth_bounded archive nx dx ny dy).mono
    (TotalWidth.totalFee_le nx dx ny dy)
  have source' : BoundedRun TotalWidth.totalWidthMachine
      (Tape.mk₂ (false :: archive)
        (fieldWord (nxContext dx ny dy) (false :: nx) (workSuffix 0 []))) 4303
      (Tape.mk₂ (false :: preservedArchive archive nx dx ny dy)
        (PA17TMRatArithmeticCopy006.workspace (TotalWidth.copiedDigits nx dx ny dy)))
      (512 * (TotalWidth.width nx dx ny dy + 1) ^ 2) := by
    simpa only [RootB23.Threshold.RoutedCopy.destinationLeft, List.replicate_zero,
      List.nil_append, preservedArchive] using source
  have copied := prepareFourCounter_bounded (preservedArchive archive nx dx ny dy)
    (TotalWidth.copiedDigits nx dx ny dy)
  rw [TotalWidth.copiedDigits_length] at copied
  have actual : BoundedRun (seqMachine TotalWidth.totalWidthMachine prepareFourCounterMachine)
      (Tape.mk₂ (false :: archive)
        (fieldWord (nxContext dx ny dy) (false :: nx) (workSuffix 0 [])))
      (rightLabel (a := 4303) (200 : Fin 201))
      (Tape.mk₂ (false :: preservedArchive archive nx dx ny dy)
        (powerWord (TotalWidth.width nx dx ny dy) 4 0))
      (512 * (TotalWidth.width nx dx ny dy + 1) ^ 2 +
        (12 * TotalWidth.width nx dx ny dy ^ 2 + 82 * TotalWidth.width nx dx ny dy + 105)) :=
    source'.seq copied
  have exit : rightLabel (a := 4303) (200 : Fin 201) = (4504 : Fin 4505) := by decide
  rw [exit] at actual
  exact actual.mono (by omega)

def reserveCap (k : Nat) : Nat := 4504 + powerStates k 4 + 1
def reserveMachine (k : Nat) : Machine (reserveCap k) :=
  seqMachine fourSourceCounterMachine (powerMachine k 4)

def reserveExit (k : Nat) : Fin (reserveCap k + 1) := rightLabel (a := 4504) (powerExit k 4)

def reserveFee (k w : Nat) : Nat :=
  512 * (w + 1) ^ 2 + 12 * w ^ 2 + 82 * w + 105 + (16 * k + 256) * (w + 1) ^ 8

theorem reserve_bounded (k : Nat) (archive nx dx ny dy : List Bool) :
    BoundedRun (reserveMachine k)
      (Tape.mk₂ (false :: archive)
        (fieldWord (nxContext dx ny dy) (false :: nx) (workSuffix 0 []))) (reserveExit k)
      (Tape.mk₂ (false :: preservedArchive archive nx dx ny dy)
        (powerWord (TotalWidth.width nx dx ny dy) 4 (k * TotalWidth.width nx dx ny dy ^ 4)))
      (reserveFee k (TotalWidth.width nx dx ny dy)) := by
  have count := fourSourceCounter_bounded archive nx dx ny dy
  obtain ⟨trace, run, time, _⟩ := quartic_gap_polynomial k
    (preservedArchive archive nx dx ny dy) (TotalWidth.width nx dx ny dy) 0
  have allocate : BoundedRun (powerMachine k 4)
      (Tape.mk₂ (false :: preservedArchive archive nx dx ny dy)
        (powerWord (TotalWidth.width nx dx ny dy) 4 0)) (powerExit k 4)
      (Tape.mk₂ (false :: preservedArchive archive nx dx ny dy)
        (powerWord (TotalWidth.width nx dx ny dy) 4 (k * TotalWidth.width nx dx ny dy ^ 4)))
      ((16 * k + 256) * (TotalWidth.width nx dx ny dy + 1) ^ 8) := by
    refine ⟨trace, ?_, ?_⟩
    · simpa only [Nat.zero_add] using run
    · simpa only [Nat.add_zero] using time
  exact count.seq allocate

theorem reserveFee_le (k w : Nat) : reserveFee k w ≤ (16 * k + 1024) * (w + 1) ^ 8 := by
  have one : 1 ≤ w + 1 := by omega
  have square : (w + 1) ^ 2 ≤ (w + 1) ^ 8 := Nat.pow_le_pow_right one (by decide)
  have linear : w ≤ (w + 1) ^ 8 := by
    have h : w + 1 ≤ (w + 1) ^ 8 := by
      simpa only [pow_one] using Nat.pow_le_pow_right one (by decide : 1 ≤ 8)
    exact (Nat.le_succ w).trans h
  have constant : 1 ≤ (w + 1) ^ 8 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right one (by decide : 0 ≤ 8)
  have wsquare : w ^ 2 ≤ (w + 1) ^ 8 := (Nat.pow_le_pow_left (Nat.le_succ w) 2).trans square
  unfold reserveFee
  nlinarith

/-- The same original bank is retained throughout a charged append/copy/
normalization/quartic execution. The allocated gap is exactly k*SUM^4. -/
theorem physical_reserve_polynomial (k : Nat) (archive nx dx ny dy : List Bool) :
    ∃ trace, RunsFrom (reserveMachine k)
      ⟨0, Tape.mk₂ (false :: archive)
        (fieldWord (nxContext dx ny dy) (false :: nx) (workSuffix 0 []))⟩ trace
      ⟨reserveExit k, Tape.mk₂ (false :: preservedArchive archive nx dx ny dy)
        (powerWord (TotalWidth.width nx dx ny dy) 4 (k * TotalWidth.width nx dx ny dy ^ 4))⟩ ∧
      trace.length ≤ (16 * k + 1024) * (TotalWidth.width nx dx ny dy + 1) ^ 8 ∧
      ∀ inputLength clock, visitedSpace (reserveMachine k) inputLength (trace.take clock) ≤
        inputLength + 2 * ((16 * k + 1024) * (TotalWidth.width nx dx ny dy + 1) ^ 8) + 1 := by
  obtain ⟨trace, run, time⟩ := reserve_bounded k archive nx dx ny dy
  have bound := reserveFee_le k (TotalWidth.width nx dx ny dy)
  refine ⟨trace, run, time.trans bound, ?_⟩
  intro inputLength clock
  have space := PSTRTMTrace002.visitedSpace_le (reserveMachine k) inputLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PhysicalReserve
