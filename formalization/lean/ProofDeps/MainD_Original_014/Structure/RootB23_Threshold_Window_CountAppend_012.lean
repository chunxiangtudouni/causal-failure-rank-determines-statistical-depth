module

public import Structure.RootB23_Threshold_RoutedLoop_007
public import Structure.PA17_TM_RatArithmetic_FarLoad_031g

/-! Reuse the actual copied-prefix loop for the four physical fields of
the bookmarked original packet. No second copy engine is introduced. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.CountAppend
open Turing PSTRTMSeq005 PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031

def wideRoute (route : FarRoute) : RootB23.Threshold.RoutedCopy.Route :=
  ⟨padMachine (by decide : 10 ≤ 100) route.out,
    padMachine (by decide : 26 ≤ 100) route.back,
    padLabel (by decide : 10 ≤ 100) route.outPort,
    padLabel (by decide : 26 ≤ 100) route.backPort⟩

theorem wide_correct (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : RouteCorrect route context finish cost) :
    RootB23.Threshold.RoutedCopy.RouteCorrect (wideRoute route) context finish cost := by
  refine ⟨correct.end_false, correct.finish_cons, ?_, ?_⟩
  · intro left later suffix
    exact bounded_pad (by decide : 10 ≤ 100) (correct.out_run left later suffix)
  · intro archive later suffix
    exact bounded_pad (by decide : 26 ≤ 100) (correct.back_run archive later suffix)

def appendMachine (route : FarRoute) : Machine 941 :=
  seqMachine (RootB23.Threshold.RoutedCopy.loopMachine (wideRoute route))
    (RootB23.Threshold.RoutedCopy.finalMachine (wideRoute route))

theorem append_bounded (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : RouteCorrect route context finish cost)
    (left digits copied : List Bool) :
    BoundedRun (appendMachine route)
      (Tape.mk₂ left (fieldWord context digits (workSuffix 0 copied))) 941
      (Tape.mk₂ (RootB23.Threshold.RoutedCopy.destinationLeft 0 (finish left digits))
        (PA17TMRatArithmeticCopy006.workspace (copied ++ digits)))
      (digits.length * (4 * (digits.length + copied.length) + 2 * cost + 37) + cost + 10) := by
  have routes := wide_correct route context finish cost correct
  have loop := RootB23.Threshold.RoutedCopy.loop_bounded (wideRoute route)
    context finish cost routes digits left copied 0
  have final := RootB23.Threshold.RoutedCopy.final_bounded (wideRoute route)
    context finish cost routes (passedLeft left digits) (copied ++ digits) 0
  rw [RootB23.Threshold.RoutedCopy.passedLeft_finish (wideRoute route)
    context finish cost routes left digits] at final
  have actual := loop.seq final
  have fee := loopFee_le cost 0 copied digits
  simp only [Nat.mul_zero, Nat.add_zero] at fee
  exact actual.mono (by omega)

def fromDestinationMachine : Machine 3 := fun q _ =>
  match q.val with
  | 0 => some (1, .move .left)
  | 1 => some (2, .move .left)
  | 2 => some (3, .move .left)
  | _ => none

theorem fromDestination_bounded (archive word : List Bool) :
    BoundedRun fromDestinationMachine
      (Tape.mk₂ (RootB23.Threshold.RoutedCopy.destinationLeft 0 archive) word) 3
      (Tape.mk₂ archive (false :: true :: false :: word)) 4 := by
  let state := fun (q : Fin 4) (west east : List Bool) =>
    (⟨q, Tape.mk₂ west east⟩ : MachineState 3)
  have actual : BoundedRun fromDestinationMachine
      (Tape.mk₂ (false :: true :: false :: archive) word) 3
      (Tape.mk₂ archive (false :: true :: false :: word)) 4 := by
    refine ⟨[state 0 (false::true::false::archive) word,
      state 1 (true::false::archive) (false::word),
      state 2 (false::archive) (true::false::word),
      state 3 archive (false::true::false::word)], ?_, by rfl⟩
    refine ⟨rfl, ?_, rfl, ?_⟩
    · simp [state, List.isChain_cons_cons, TM0.step, fromDestinationMachine, Tape.mk₂]
    · simp [TM0.step, fromDestinationMachine]
  exact actual

def recoverMachine (route : FarRoute) : Machine 104 :=
  seqMachine fromDestinationMachine (wideRoute route).back

theorem recover_bounded (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : RouteCorrect route context finish cost)
    (archive digits copied : List Bool) :
    BoundedRun (recoverMachine route)
      (Tape.mk₂ (RootB23.Threshold.RoutedCopy.destinationLeft 0
        (finish (false :: archive) digits)) (PA17TMRatArithmeticCopy006.workspace copied))
      (rightLabel (a := 3) (wideRoute route).backPort)
      (Tape.mk₂ (false :: archive) (fieldWord context digits (workSuffix 0 copied)))
      (2 * digits.length + cost + 4) := by
  have back := (wide_correct route context finish cost correct).back_run archive digits (workSuffix 0 copied)
  have actual := (fromDestination_bounded (finish (false :: archive) digits)
    (PA17TMRatArithmeticCopy006.workspace copied)).seq back
  exact actual.mono (by omega)

def recoverAppendMachine (route : FarRoute) : Machine 1046 :=
  seqMachine (recoverMachine route) (appendMachine route)

theorem recoverAppend_bounded (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : RouteCorrect route context finish cost)
    (archive digits copied : List Bool) :
    BoundedRun (recoverAppendMachine route)
      (Tape.mk₂ (RootB23.Threshold.RoutedCopy.destinationLeft 0
        (finish (false :: archive) digits)) (PA17TMRatArithmeticCopy006.workspace copied)) 1046
      (Tape.mk₂ (RootB23.Threshold.RoutedCopy.destinationLeft 0
        (finish (false :: archive) digits))
        (PA17TMRatArithmeticCopy006.workspace (copied ++ digits)))
      (digits.length * (4 * (digits.length + copied.length) + 2 * cost + 37) +
        2 * digits.length + 2 * cost + 14) := by
  have actual := (recover_bounded route context finish cost correct archive digits copied).seq
    (append_bounded route context finish cost correct (false :: archive) digits copied)
  exact actual.mono (by omega)

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.CountAppend
