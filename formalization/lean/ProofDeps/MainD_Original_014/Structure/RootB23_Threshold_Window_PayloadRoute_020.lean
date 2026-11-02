module

public import Structure.RootB23_Threshold_Window_PayloadPorts_019

/-! Concrete second/third/fourth-field routes. The original bank, four
counters, allocated gap, both gap anchors, and every earlier payload field
are traversed by fixed finite code. A copied bit is still carried by the
existing RoutedLoop007 implementation; this file adds no bit-copy kernel. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadRoute
open Turing PSTRTMSeq005 PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticAllocate013

def context (old : List Bool) (n gap : Nat) (slot : Fin 3) (a b c : List Bool) : List Bool :=
  GapRoute.context old n gap ++ false :: true :: false :: PayloadPorts.core slot a b c

def finish (old : List Bool → List Bool → List Bool) (n gap : Nat) (slot : Fin 3)
    (a b c left later : List Bool) : List Bool :=
  PayloadPorts.finish slot (false :: true :: false :: GapRoute.finish old n gap left later) a b c

def oldGapMachine (old : FarRoute) : Machine 32 :=
  seqMachine (GapRoute.sourceToGapMachine old) (gapSeekMachine .right)
def enterPayloadMachine (old : FarRoute) : Machine 37 :=
  seqMachine (oldGapMachine old) (PayloadPorts.fourMachine .right)
def outMachine (old : FarRoute) (slot : Fin 3) : Machine 51 :=
  seqMachine (enterPayloadMachine old) (PayloadPorts.outMachine slot)

def exitPayloadMachine (slot : Fin 3) : Machine 30 :=
  seqMachine (PayloadPorts.backMachine slot) (PayloadPorts.fourMachine .left)
def oldGapBackMachine (slot : Fin 3) : Machine 32 :=
  seqMachine (exitPayloadMachine slot) (gapSeekMachine .left)
def counterBackMachine (slot : Fin 3) : Machine 64 :=
  seqMachine (oldGapBackMachine slot) counterFourBackMachine
def oldFooterMachine (slot : Fin 3) : Machine 68 :=
  seqMachine (counterBackMachine slot) CountAppend.fromDestinationMachine
def backMachine (old : FarRoute) (slot : Fin 3) : Machine 95 :=
  seqMachine (oldFooterMachine slot) old.back

def route (old : FarRoute) (slot : Fin 3) : RootB23.Threshold.RoutedCopy.Route :=
  ⟨padMachine (by decide : 51 ≤ 100) (outMachine old slot),
    padMachine (by decide : 95 ≤ 100) (backMachine old slot),
    padLabel (by decide : 51 ≤ 100) (rightLabel (a := 37) (PayloadPorts.outPort slot)),
    padLabel (by decide : 95 ≤ 100) (rightLabel (a := 68) old.backPort)⟩

theorem correct (oldRoute : FarRoute) (oldContext : List Bool)
    (oldFinish : List Bool → List Bool → List Bool) (cost : Nat)
    (old : RouteCorrect oldRoute oldContext oldFinish cost)
    (n gap : Nat) (slot : Fin 3) (a b c : List Bool) :
    RootB23.Threshold.RoutedCopy.RouteCorrect (route oldRoute slot)
      (context oldContext n gap slot a b c) (finish oldFinish n gap slot a b c)
      (cost + 8 * n + gap + 2 * PayloadPorts.width slot a b c + 100) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases oldContext with
    | nil => rfl
    | cons bit rest =>
      have bitFalse : bit = false := old.end_false
      subst bit
      rfl
  · intro left bit later
    unfold finish GapRoute.finish
    rw [old.finish_cons]
  · intro left later suffix
    let footer := oldFinish left later
    let countArchive := true :: false :: footer
    let counterLeft := false :: counterArchive countArchive (List.replicate n false) 4
    let gapLeft := List.replicate gap false ++ true :: counterLeft
    let payloadLeft := false :: true :: false :: true :: gapLeft
    let payload := PayloadPorts.core slot a b c ++ false :: suffix
    let word := GapRoute.counterWords n ++ true ::
      (List.replicate gap false ++ true :: false :: true :: false :: payload)
    let tail := true :: false :: word
    have original := old.out_run left later tail
    have counter := GapRoute.toCounter_bounded footer word
    have fields := MarshalAnchor.counterFourForward_bounded countArchive (List.replicate n false)
      (true :: (List.replicate gap false ++ true :: false :: true :: false :: payload))
    have cross : BoundedRun (gapSeekMachine .right)
        (Tape.mk₂ counterLeft
          (true :: (List.replicate gap false ++ true :: false :: true :: false :: payload))) 1
        (Tape.mk₂ gapLeft (true :: false :: true :: false :: payload)) (gap + 2) :=
      ⟨PA17TMRatArithmeticRecordNav032.gapRightTrace gap counterLeft true (false :: true :: false :: payload),
        PA17TMRatArithmeticRecordNav032.gapRight_runsFrom gap counterLeft true (false :: true :: false :: payload),
        by rw [PA17TMRatArithmeticRecordNav032.gapRightTrace_length]⟩
    have enter := PayloadPorts.fourRight_bounded gapLeft payload
    have scan := PayloadPorts.out_bounded slot payloadLeft a b c suffix
    dsimp only [footer, countArchive, counterLeft, gapLeft, payloadLeft, payload, word, tail]
      at original counter fields cross enter scan
    simp only [GapRoute.counterWords, List.append_assoc] at original counter fields cross enter scan
    have actual := ((((original.seq counter).seq fields).seq cross).seq enter).seq scan
    have padded := bounded_pad (by decide : 51 ≤ 100) actual
    simpa only [route, outMachine, enterPayloadMachine, oldGapMachine,
      GapRoute.sourceToGapMachine, GapRoute.sourceToCounterMachine,
      context, finish, GapRoute.context, GapRoute.finish,
      RootB23.Threshold.RoutedCopy.fieldWord, fieldWord, GapRoute.counterWords,
      List.append_assoc, List.cons_append, List.nil_append] using padded.mono
        (by simp only [List.length_replicate]; omega :
          ((((2 * later.length + cost + 4) + (8 * (List.replicate n false).length + 16)) +
            (gap + 2)) + 5) + (2 * PayloadPorts.width slot a b c + 14) ≤
              2 * later.length + (cost + 8 * n + gap + 2 * PayloadPorts.width slot a b c + 100))
  · intro archive later suffix
    let footer := oldFinish (false :: archive) later
    let countArchive := true :: false :: footer
    let counterLeft := false :: counterArchive countArchive (List.replicate n false) 4
    let gapLeft := List.replicate gap false ++ true :: counterLeft
    let payloadArchive := true :: false :: true :: gapLeft
    let payload := PayloadPorts.core slot a b c ++ false :: suffix
    let word := GapRoute.counterWords n ++ true ::
      (List.replicate gap false ++ true :: false :: true :: false :: payload)
    let tail := true :: false :: word
    have scan := PayloadPorts.back_bounded slot payloadArchive a b c suffix
    have exit := PayloadPorts.fourLeft_bounded gapLeft payload
    have cross : BoundedRun (gapSeekMachine .left)
        (Tape.mk₂ gapLeft (true :: false :: true :: false :: payload)) 1
        (Tape.mk₂ counterLeft
          (true :: (List.replicate gap false ++ true :: false :: true :: false :: payload))) (gap + 2) :=
      ⟨returnGapTrace gap counterLeft (false :: true :: false :: payload),
        returnGap_runsFrom gap counterLeft (false :: true :: false :: payload), by rw [returnGap_length]⟩
    have fields := counterFourBack_bounded countArchive (List.replicate n false)
      (true :: (List.replicate gap false ++ true :: false :: true :: false :: payload))
    have fromCount := CountAppend.fromDestination_bounded footer word
    have original := old.back_run archive later tail
    dsimp only [footer, countArchive, counterLeft, gapLeft, payloadArchive, payload, word, tail]
      at scan exit cross fields fromCount original
    simp only [GapRoute.counterWords, RootB23.Threshold.RoutedCopy.destinationLeft, List.replicate_zero,
      List.nil_append, List.append_assoc] at scan exit cross fields fromCount original
    have actual := ((((scan.seq exit).seq cross).seq fields).seq fromCount).seq original
    have padded := bounded_pad (by decide : 95 ≤ 100) actual
    simpa only [route, backMachine, oldFooterMachine, counterBackMachine,
      oldGapBackMachine, exitPayloadMachine, context, finish, GapRoute.context, GapRoute.finish,
      RootB23.Threshold.RoutedCopy.fieldWord, fieldWord, GapRoute.counterWords,
      List.append_assoc, List.cons_append, List.nil_append] using padded.mono
        (by simp only [List.length_replicate]; omega :
          ((((2 * PayloadPorts.width slot a b c + 23 + 5) + (gap + 2)) +
            (8 * (List.replicate n false).length + 28)) + 4) + (2 * later.length + cost) ≤
              2 * later.length + (cost + 8 * n + gap + 2 * PayloadPorts.width slot a b c + 100))

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadRoute
