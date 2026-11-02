module

public import Structure.RootB23_Threshold_Window_PayloadRoute_020
public import Structure.RootB23_Threshold_Window_PayloadInit_022

/-! The actual copy/restore, new-anchor, and final rewind/clear steps of
the four-field marshaller. All bit copying is the frozen RoutedLoop007;
the observed bit is selected by an actual finite-control row. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadSteps
open Turing PSTRTMSeq005
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticAllocate013
open PA17TMRatArithmeticAllocatePass023

def copyMachine (route : RootB23.Threshold.RoutedCopy.Route) (which memory : Nat) : Machine 1164 :=
  seqMachine (RootB23.Threshold.RoutedCopy.copyMachine route) (setMarkerMachine (memory.testBit which))

def copyFee (tail : List Bool) (cost : Nat) : Nat :=
  4 * (false :: tail).length ^ 2 + (2 * cost + 41) * (false :: tail).length + 3 * cost + 31

theorem copy_bounded (route : RootB23.Threshold.RoutedCopy.Route) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : RootB23.Threshold.RoutedCopy.RouteCorrect route context finish cost)
    (which memory : Nat) (archive tail : List Bool) :
    BoundedRun (copyMachine route which memory)
      (Tape.mk₂ (false :: archive)
        (RootB23.Threshold.RoutedCopy.fieldWord context (false :: tail) (workSuffix 0 []))) 1164
      (Tape.mk₂ (RootB23.Threshold.RoutedCopy.destinationLeft 0 (finish (false :: archive) (false :: tail)))
        (PA17TMRatArithmeticCopy006.workspace (memory.testBit which :: tail)))
      (copyFee tail cost) := by
  have copy := RootB23.Threshold.RoutedCopy.copy_bounded route context finish cost correct archive (false :: tail) 0
  simp only [Nat.mul_zero, Nat.add_zero] at copy
  have restore : BoundedRun (setMarkerMachine (memory.testBit which))
      (Tape.mk₂ (RootB23.Threshold.RoutedCopy.destinationLeft 0 (finish (false :: archive) (false :: tail)))
        (PA17TMRatArithmeticCopy006.workspace (false :: tail))) 1
      (Tape.mk₂ (RootB23.Threshold.RoutedCopy.destinationLeft 0 (finish (false :: archive) (false :: tail)))
        (PA17TMRatArithmeticCopy006.workspace (memory.testBit which :: tail))) 2 :=
    ⟨setMarkerTrace false (memory.testBit which) _ _, setMarker_runsFrom false (memory.testBit which) _ _, by rfl⟩
  exact (copy.seq restore).mono (by unfold copyFee; omega)

def nextAnchorMachine : Machine 3 := fun q _ =>
  match q.val with
  | 0 => some (1, .move .right)
  | 1 => some (2, .write true)
  | 2 => some (3, .move .left)
  | _ => none

theorem nextAnchor_bounded (left : List Bool) :
    BoundedRun nextAnchorMachine (Tape.mk₂ left [false]) 3
      (Tape.mk₂ left (false :: workSuffix 0 [])) 4 := by
  let state := fun (q : Fin 4) (west east : List Bool) => (⟨q, Tape.mk₂ west east⟩ : MachineState 3)
  have actual : BoundedRun nextAnchorMachine (Tape.mk₂ left [false]) 3
      (Tape.mk₂ left [false,true]) 4 := by
    refine ⟨[state 0 left [false], state 1 (false::left) [],
      state 2 (false::left) [true], state 3 left [false,true]], ?_, by rfl⟩
    refine ⟨rfl, ?_, rfl, ?_⟩
    · simp [state, List.isChain_cons_cons, TM0.step, nextAnchorMachine, Tape.mk₂]
    · simp [TM0.step, nextAnchorMachine]
  have padding := PayloadInit.tape_three_false left [false,true]
  change Tape.mk₂ left (false :: workSuffix 0 []) = Tape.mk₂ left [false,true] at padding
  rw [padding]
  exact actual

def nextMachine (route : RootB23.Threshold.RoutedCopy.Route) : Machine 106 :=
  seqMachine (seqMachine outDyMachine nextAnchorMachine) route.back

theorem next_bounded (route : RootB23.Threshold.RoutedCopy.Route) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : RootB23.Threshold.RoutedCopy.RouteCorrect route context finish cost)
    (archive digits left previous : List Bool)
    (boundary : finish (false :: archive) digits = PA17TMRatArithmeticAllocatePass023.pushField left previous) :
    BoundedRun (nextMachine route)
      (Tape.mk₂ left (PA17TMRatArithmeticCopy006.workspace previous))
      (rightLabel (a := 5) route.backPort)
      (Tape.mk₂ (false :: archive) (RootB23.Threshold.RoutedCopy.fieldWord context digits (workSuffix 0 [])))
      (2 * previous.length + 2 * digits.length + cost + 6) := by
  have scan := PayloadNav.scan_bounded left previous []
  simp only [List.append_nil] at scan
  have anchor := nextAnchor_bounded (PA17TMRatArithmeticAllocatePass023.pushField left previous)
  have back := correct.back_run archive digits (workSuffix 0 [])
  rw [boundary] at back
  exact ((scan.seq anchor).seq back).mono
    (b := 2 * previous.length + 2 * digits.length + cost + 6) (by omega)

def word4 (a b c d suffix : List Bool) : List Bool :=
  PA17TMRatArithmeticCopy006.workspace a ++ true :: false :: PayloadNav.word3 b c d suffix

def returnFirstMachine : Machine 29 := seqMachine CountAppend.fromDestinationMachine PayloadNav.back3Machine

theorem returnFirst_bounded (archive a b c d suffix : List Bool) :
    BoundedRun returnFirstMachine
      (Tape.mk₂ (PayloadNav.nextLeft (PayloadNav.nextLeft (PayloadNav.nextLeft (false :: archive) a) b) c)
        (PA17TMRatArithmeticCopy006.workspace d ++ suffix)) 29
      (Tape.mk₂ (false :: archive) (word4 a b c d suffix))
      (2 * (a.length + b.length + c.length) + 27) := by
  have connector := CountAppend.fromDestination_bounded
    (PA17TMRatArithmeticAllocatePass023.pushField (PayloadNav.nextLeft (PayloadNav.nextLeft (false :: archive) a) b) c)
    (PA17TMRatArithmeticCopy006.workspace d ++ suffix)
  have back := PayloadNav.back3_bounded archive a b c
    (true :: false :: (PA17TMRatArithmeticCopy006.workspace d ++ suffix))
  have actual := connector.seq back
  have exit : rightLabel (a := 3) (25 : Fin 26) = (29 : Fin 30) := by decide
  rw [exit] at actual
  simpa only [returnFirstMachine, word4, PayloadNav.word3, PayloadNav.word2,
    PayloadNav.nextLeft, RootB23.Threshold.RoutedCopy.destinationLeft, List.replicate_zero,
    List.nil_append, List.append_assoc] using actual.mono (by omega :
      4 + (2 * (a.length + b.length + c.length) + 23) ≤ 2 * (a.length + b.length + c.length) + 27)

def clearPrefixMachine : Machine 10 := fun q _ =>
  match q.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .move .left)
  | 2 => some (3, .write false)
  | 3 => some (4, .move .left)
  | 4 => some (5, .move .left)
  | 5 => some (6, .write false)
  | 6 => some (7, .move .right)
  | 7 => some (8, .move .right)
  | 8 => some (9, .move .right)
  | 9 => some (10, .move .right)
  | _ => none

theorem clearPrefix_bounded (left right : List Bool) :
    BoundedRun clearPrefixMachine (Tape.mk₂ (false :: true :: false :: true :: left) right) 10
      (Tape.mk₂ (false :: false :: false :: false :: left) right) 11 := by
  let state := fun (q : Fin 11) (west east : List Bool) => (⟨q, Tape.mk₂ west east⟩ : MachineState 10)
  refine ⟨[state 0 (false::true::false::true::left) right,
    state 1 (true::false::true::left) (false::right),
    state 2 (false::true::left) (true::false::right),
    state 3 (false::true::left) (false::false::right),
    state 4 (true::left) (false::false::false::right),
    state 5 left (true::false::false::false::right),
    state 6 left (false::false::false::false::right),
    state 7 (false::left) (false::false::false::right),
    state 8 (false::false::left) (false::false::right),
    state 9 (false::false::false::left) (false::right),
    state 10 (false::false::false::false::left) right], ?_, by rfl⟩
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [state, List.isChain_cons_cons, TM0.step, clearPrefixMachine, Tape.mk₂]
  · simp [TM0.step, clearPrefixMachine]

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadSteps
