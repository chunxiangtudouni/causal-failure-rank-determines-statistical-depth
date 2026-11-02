module

public import Structure.RootB23_Threshold_Window_CountAppend_012

/-! One fixed finite table appends all four real bookmarked fields to the
same destination. Their widths add. The destination is never reinitialized
between fields; the complete source bank and arbitrary WEST base remain. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.TotalWidth
open Turing PSTRTMSeq005
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticAllocatePass023
open CountAppend

def copiedDigits (nx dx ny dy : List Bool) : List Bool :=
  (false :: nx) ++ (false :: dx) ++ (false :: ny) ++ (false :: dy)

def width (nx dx ny dy : List Bool) : Nat :=
  (false :: nx).length + (false :: dx).length + (false :: ny).length + (false :: dy).length

def bankLeft (archive nx dx ny dy : List Bool) : List Bool :=
  nxFinish dx ny dy (false :: archive) (false :: nx)

def dxArchive (archive nx : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks (false :: nx).reverse ++ false :: archive

def nyArchive (archive nx dx : List Bool) : List Bool :=
  false :: pushField (pushField (false :: archive) (false :: nx)) (false :: dx)

def dyArchive (archive nx dx ny : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks (false :: ny).reverse ++ false :: nyArchive archive nx dx

theorem dx_finish (archive nx dx ny dy : List Bool) :
    dxFinish ny dy (false :: dxArchive archive nx) (false :: dx) = bankLeft archive nx dx ny dy := rfl

theorem ny_finish (archive nx dx ny dy : List Bool) :
    nyFinish dy (false :: nyArchive archive nx dx) (false :: ny) = bankLeft archive nx dx ny dy := rfl

theorem dy_finish (archive nx dx ny dy : List Bool) :
    dyFinish (false :: dyArchive archive nx dx ny) (false :: dy) = bankLeft archive nx dx ny dy := rfl

def numCost (dx ny dy : List Bool) : Nat :=
  2 * ((false :: dx).length + (false :: ny).length + (false :: dy).length) + 23
def denCost (ny dy : List Bool) : Nat := 2 * ((false :: ny).length + (false :: dy).length) + 18
def riskNumCost (dy : List Bool) : Nat := 2 * (false :: dy).length + 10

def copyFee (digits : List Bool) (cost : Nat) : Nat :=
  4 * digits.length ^ 2 + (2 * cost + 41) * digits.length + 3 * cost + 29

def nextFee (digits copied : List Bool) (cost : Nat) : Nat :=
  digits.length * (4 * (digits.length + copied.length) + 2 * cost + 37) +
    2 * digits.length + 2 * cost + 14

def totalFee (nx dx ny dy : List Bool) : Nat :=
  copyFee (false :: nx) (numCost dx ny dy) +
    nextFee (false :: dx) (false :: nx) (denCost ny dy) +
    nextFee (false :: ny) ((false :: nx) ++ (false :: dx)) (riskNumCost dy) +
    nextFee (false :: dy) (((false :: nx) ++ (false :: dx)) ++ (false :: ny)) 5

def firstMachine : Machine 1162 := RootB23.Threshold.RoutedCopy.copyMachine (wideRoute nxRoute)
def firstTwoMachine : Machine 2209 := seqMachine firstMachine (recoverAppendMachine dxRoute)
def firstThreeMachine : Machine 3256 := seqMachine firstTwoMachine (recoverAppendMachine nyRoute)
def totalWidthMachine : Machine 4303 := seqMachine firstThreeMachine (recoverAppendMachine dyRoute)

theorem totalWidth_bounded (archive nx dx ny dy : List Bool) :
    BoundedRun totalWidthMachine
      (Tape.mk₂ (false :: archive)
        (fieldWord (nxContext dx ny dy) (false :: nx) (workSuffix 0 []))) 4303
      (Tape.mk₂ (RootB23.Threshold.RoutedCopy.destinationLeft 0 (bankLeft archive nx dx ny dy))
        (PA17TMRatArithmeticCopy006.workspace (copiedDigits nx dx ny dy)))
      (totalFee nx dx ny dy) := by
  have first := RootB23.Threshold.RoutedCopy.copy_bounded (wideRoute nxRoute)
    (nxContext dx ny dy) (nxFinish dx ny dy) (numCost dx ny dy)
    (wide_correct nxRoute _ _ _ (nx_route_correct dx ny dy)) archive (false :: nx) 0
  have second := recoverAppend_bounded dxRoute (dxContext ny dy) (dxFinish ny dy)
    (denCost ny dy) (dx_route_correct ny dy) (dxArchive archive nx) (false :: dx) (false :: nx)
  have third := recoverAppend_bounded nyRoute (nyContext dy) (nyFinish dy)
    (riskNumCost dy) (ny_route_correct dy) (nyArchive archive nx dx) (false :: ny)
    ((false :: nx) ++ (false :: dx))
  have fourth := recoverAppend_bounded dyRoute [] dyFinish 5 dy_route_correct
    (dyArchive archive nx dx ny) (false :: dy)
    (((false :: nx) ++ (false :: dx)) ++ (false :: ny))
  rw [dx_finish] at second
  rw [ny_finish] at third
  rw [dy_finish] at fourth
  have actual := ((first.seq second).seq third).seq fourth
  have exit : rightLabel (a := 3256) (1046 : Fin 1047) = (4303 : Fin 4304) := by decide
  rw [exit] at actual
  simpa only [totalWidthMachine, firstThreeMachine, firstTwoMachine, firstMachine,
    totalFee, copyFee, nextFee, copiedDigits, bankLeft, Nat.mul_zero, Nat.add_zero,
    RootB23.Threshold.RoutedCopy.fieldWord, fieldWord, List.append_assoc] using actual

theorem copiedDigits_length (nx dx ny dy : List Bool) :
    (copiedDigits nx dx ny dy).length = width nx dx ny dy := by
  simp only [copiedDigits, width, List.length_append]

theorem copyFee_le (digits : List Bool) (cost w : Nat)
    (digitsBound : digits.length ≤ w) (costBound : cost ≤ 2 * w + 23) :
    copyFee digits cost ≤ 128 * (w + 1) ^ 2 := by
  have square := Nat.mul_le_mul digitsBound digitsBound
  have mixed := Nat.mul_le_mul costBound digitsBound
  unfold copyFee
  nlinarith

theorem nextFee_le (digits copied : List Bool) (cost w : Nat)
    (digitsBound : digits.length ≤ w) (copiedBound : copied.length ≤ w)
    (costBound : cost ≤ 2 * w + 23) :
    nextFee digits copied cost ≤ 128 * (w + 1) ^ 2 := by
  have coefficient : 4 * (digits.length + copied.length) + 2 * cost + 37 ≤ 12 * w + 83 := by omega
  have product := Nat.mul_le_mul digitsBound coefficient
  unfold nextFee
  nlinarith

theorem totalFee_le (nx dx ny dy : List Bool) :
    totalFee nx dx ny dy ≤ 512 * (width nx dx ny dy + 1) ^ 2 := by
  let w := width nx dx ny dy
  have nxBound : (false :: nx).length ≤ w := by unfold w width; omega
  have dxBound : (false :: dx).length ≤ w := by unfold w width; omega
  have nyBound : (false :: ny).length ≤ w := by unfold w width; omega
  have dyBound : (false :: dy).length ≤ w := by unfold w width; omega
  have firstCost : numCost dx ny dy ≤ 2 * w + 23 := by unfold numCost w width; omega
  have secondCost : denCost ny dy ≤ 2 * w + 23 := by unfold denCost w width; omega
  have thirdCost : riskNumCost dy ≤ 2 * w + 23 := by unfold riskNumCost w width; omega
  have first := copyFee_le (false :: nx) (numCost dx ny dy) w nxBound firstCost
  have second := nextFee_le (false :: dx) (false :: nx) (denCost ny dy) w dxBound nxBound secondCost
  have third := nextFee_le (false :: ny) ((false :: nx) ++ (false :: dx))
    (riskNumCost dy) w nyBound (by simp only [List.length_append]; unfold w width; omega) thirdCost
  have fourth := nextFee_le (false :: dy) (((false :: nx) ++ (false :: dx)) ++ (false :: ny))
    5 w dyBound (by simp only [List.length_append]; unfold w width; omega) (by omega)
  change totalFee nx dx ny dy ≤ 512 * (w + 1) ^ 2
  unfold totalFee
  omega

theorem totalWidth_polynomial (archive nx dx ny dy : List Bool) :
    ∃ trace, RunsFrom totalWidthMachine
      ⟨0, Tape.mk₂ (false :: archive)
        (fieldWord (nxContext dx ny dy) (false :: nx) (workSuffix 0 []))⟩ trace
      ⟨4303, Tape.mk₂ (RootB23.Threshold.RoutedCopy.destinationLeft 0 (bankLeft archive nx dx ny dy))
        (PA17TMRatArithmeticCopy006.workspace (copiedDigits nx dx ny dy))⟩ ∧
      (copiedDigits nx dx ny dy).length = width nx dx ny dy ∧
      trace.length ≤ 512 * (width nx dx ny dy + 1) ^ 2 ∧
      ∀ inputLength clock, visitedSpace totalWidthMachine inputLength (trace.take clock) ≤
        inputLength + 1024 * (width nx dx ny dy + 1) ^ 2 + 1 := by
  obtain ⟨trace, run, time⟩ := totalWidth_bounded archive nx dx ny dy
  have budget := totalFee_le nx dx ny dy
  refine ⟨trace, run, copiedDigits_length nx dx ny dy, time.trans budget, ?_⟩
  intro inputLength clock
  have space := PSTRTMTrace002.visitedSpace_le totalWidthMachine inputLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.TotalWidth
