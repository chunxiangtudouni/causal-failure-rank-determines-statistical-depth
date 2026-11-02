module

public import Structure.RootB23_Threshold_Window_MarshalAnchor_016

/-! A concrete source-to-far-payload route across the four counted fields
and the actually allocated zero gap. Both TRUE gap endpoints belong to the
route's context. No arbitrary suffix is read as an alleged marker. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.GapRoute
open Turing PSTRTMSeq005 PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticAllocate013
open MarshalAnchor

def counterWords (n : Nat) : List Bool :=
  PA17TMRatArithmeticCopy006.workspace (List.replicate n false) ++
    (PA17TMRatArithmeticCopy006.workspace (List.replicate n false) ++
      (PA17TMRatArithmeticCopy006.workspace (List.replicate n false) ++
        PA17TMRatArithmeticCopy006.workspace (List.replicate n false)))

def context (old : List Bool) (n gap : Nat) : List Bool :=
  old ++ false :: true :: false :: (counterWords n ++ true :: (List.replicate gap false ++ [true]))

def finish (old : List Bool → List Bool → List Bool) (n gap : Nat)
    (left later : List Bool) : List Bool :=
  true :: (List.replicate gap false ++ true :: false ::
    counterArchive (true :: false :: old left later) (List.replicate n false) 4)

def toCounterMachine : Machine 3 := fun q _ =>
  match q.val with
  | 0 => some (1, .move .right)
  | 1 => some (2, .move .right)
  | 2 => some (3, .move .right)
  | _ => none

theorem toCounter_bounded (archive word : List Bool) :
    BoundedRun toCounterMachine (Tape.mk₂ archive (false :: true :: false :: word)) 3
      (Tape.mk₂ (false :: true :: false :: archive) word) 4 := by
  let state := fun (q : Fin 4) (west east : List Bool) =>
    (⟨q, Tape.mk₂ west east⟩ : MachineState 3)
  refine ⟨[state 0 archive (false::true::false::word),
    state 1 (false::archive) (true::false::word),
    state 2 (true::false::archive) (false::word),
    state 3 (false::true::false::archive) word], ?_, by rfl⟩
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [state, List.isChain_cons_cons, TM0.step, toCounterMachine, Tape.mk₂]
  · simp [TM0.step, toCounterMachine]

def sourceToCounterMachine (route : FarRoute) : Machine 14 := seqMachine route.out toCounterMachine
def sourceToGapMachine (route : FarRoute) : Machine 30 :=
  seqMachine (sourceToCounterMachine route) counterFourForwardMachine
def acrossGapMachine (route : FarRoute) : Machine 32 :=
  seqMachine (sourceToGapMachine route) (gapSeekMachine .right)
def outMachine (route : FarRoute) : Machine 34 :=
  seqMachine (acrossGapMachine route) PA17TMRatArithmeticParse002.footerMachine

def backAcrossMachine : Machine 3 :=
  seqMachine PA17TMRatArithmeticParse002.backOneMachine (gapSeekMachine .left)
def backCountersMachine : Machine 35 := seqMachine backAcrossMachine counterFourBackMachine
def backFooterMachine : Machine 39 := seqMachine backCountersMachine CountAppend.fromDestinationMachine
def backMachine (route : FarRoute) : Machine 66 := seqMachine backFooterMachine route.back

def route (old : FarRoute) : RootB23.Threshold.RoutedCopy.Route :=
  ⟨padMachine (by decide : 34 ≤ 100) (outMachine old),
    padMachine (by decide : 66 ≤ 100) (backMachine old),
    padLabel (by decide : 34 ≤ 100) 34,
    padLabel (by decide : 66 ≤ 100) (rightLabel (a := 39) old.backPort)⟩

theorem correct (oldRoute : FarRoute) (oldContext : List Bool)
    (oldFinish : List Bool → List Bool → List Bool) (cost : Nat)
    (old : RouteCorrect oldRoute oldContext oldFinish cost) (n gap : Nat) :
    RootB23.Threshold.RoutedCopy.RouteCorrect (route oldRoute) (context oldContext n gap)
      (finish oldFinish n gap) (cost + 8 * n + gap + 40) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases oldContext with
    | nil => rfl
    | cons bit rest =>
      have bitFalse : bit = false := old.end_false
      subst bit
      rfl
  · intro left bit later
    unfold finish
    rw [old.finish_cons]
  · intro left later suffix
    let footer := oldFinish left later
    let countArchive := true :: false :: footer
    let counterLeft := false :: counterArchive countArchive (List.replicate n false) 4
    let tail := true :: false :: (counterWords n ++ true :: (List.replicate gap false ++ true :: false :: suffix))
    have original := old.out_run left later tail
    have counter := toCounter_bounded footer
      (counterWords n ++ true :: (List.replicate gap false ++ true :: false :: suffix))
    have fields := counterFourForward_bounded countArchive (List.replicate n false)
      (true :: (List.replicate gap false ++ true :: false :: suffix))
    have cross : BoundedRun (gapSeekMachine .right)
        (Tape.mk₂ counterLeft (true :: (List.replicate gap false ++ true :: false :: suffix))) 1
        (Tape.mk₂ (List.replicate gap false ++ true :: counterLeft) (true :: false :: suffix)) (gap + 2) :=
      ⟨PA17TMRatArithmeticRecordNav032.gapRightTrace gap counterLeft true (false :: suffix),
        PA17TMRatArithmeticRecordNav032.gapRight_runsFrom gap counterLeft true (false :: suffix),
        by rw [PA17TMRatArithmeticRecordNav032.gapRightTrace_length]⟩
    have last := footer_any_bounded (List.replicate gap false ++ true :: counterLeft) true (false :: suffix)
    dsimp only [footer, countArchive, counterLeft, tail] at original counter fields cross last
    simp only [counterWords, List.append_assoc] at original counter fields cross last
    have actual := (((original.seq counter).seq fields).seq cross).seq last
    have exit : rightLabel (a := 32) (1 : Fin 2) = (34 : Fin 35) := by decide
    rw [exit] at actual
    have padded := bounded_pad (by decide : 34 ≤ 100) actual
    simpa only [route, outMachine, acrossGapMachine, sourceToGapMachine, sourceToCounterMachine,
      context, finish, RootB23.Threshold.RoutedCopy.fieldWord, fieldWord,
      counterWords, footer, countArchive, counterLeft, tail,
      List.append_assoc, List.cons_append, List.nil_append] using padded.mono
        (by simp only [List.length_replicate]; omega :
          (((2 * later.length + cost + 4) + (8 * (List.replicate n false).length + 16)) +
            (gap + 2)) + 2 ≤ 2 * later.length + (cost + 8 * n + gap + 40))
  · intro archive later suffix
    let footer := oldFinish (false :: archive) later
    let countArchive := true :: false :: footer
    let counterLeft := false :: counterArchive countArchive (List.replicate n false) 4
    let word := counterWords n ++ true :: (List.replicate gap false ++ true :: false :: suffix)
    let tail := true :: false :: word
    have back : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
        (Tape.mk₂ (true :: (List.replicate gap false ++ true :: counterLeft)) (false :: suffix)) 1
        (Tape.mk₂ (List.replicate gap false ++ true :: counterLeft) (true :: false :: suffix)) 2 :=
      ⟨PA17TMRatArithmeticParse002.backOneTrace _ true _,
        PA17TMRatArithmeticParse002.backOne_runsFrom _ true _, by rfl⟩
    have cross : BoundedRun (gapSeekMachine .left)
        (Tape.mk₂ (List.replicate gap false ++ true :: counterLeft) (true :: false :: suffix)) 1
        (Tape.mk₂ counterLeft (true :: (List.replicate gap false ++ true :: false :: suffix))) (gap + 2) :=
      ⟨returnGapTrace gap counterLeft (false :: suffix),
        returnGap_runsFrom gap counterLeft (false :: suffix), by rw [returnGap_length]⟩
    have fields := counterFourBack_bounded countArchive (List.replicate n false)
      (true :: (List.replicate gap false ++ true :: false :: suffix))
    have fromCount := CountAppend.fromDestination_bounded footer word
    have original := old.back_run archive later tail
    dsimp only [footer, countArchive, counterLeft, word, tail] at back cross fields fromCount original
    simp only [counterWords, RootB23.Threshold.RoutedCopy.destinationLeft, List.replicate_zero,
      List.nil_append, List.append_assoc] at back cross fields fromCount original
    have actual := (((back.seq cross).seq fields).seq fromCount).seq original
    have padded := bounded_pad (by decide : 66 ≤ 100) actual
    simpa only [route, backMachine, backFooterMachine, backCountersMachine, backAcrossMachine,
      context, finish, RootB23.Threshold.RoutedCopy.fieldWord, fieldWord,
      counterWords, footer, countArchive, counterLeft, word, tail,
      List.append_assoc, List.cons_append, List.nil_append] using padded.mono
        (by simp only [List.length_replicate]; omega :
          (((2 + (gap + 2)) + (8 * (List.replicate n false).length + 28)) + 4) +
            (2 * later.length + cost) ≤ 2 * later.length + (cost + 8 * n + gap + 40))

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.GapRoute
