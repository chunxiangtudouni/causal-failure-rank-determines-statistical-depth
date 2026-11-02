module

public import Structure.RootB23_Threshold_Window_PhysicalReserve_014

/-! The left end of the allocated gap becomes a real permanent TRUE anchor.
The program returns across all four actual counters and the real count-work
anchor to the original NUM source. This is the physical entry for payload
marshalling; a later gap-return never guesses a distance or a false stop. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.MarshalAnchor
open Turing PSTRTMSeq005
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticAllocatePass023

theorem footer_any_bounded (left : List Bool) (bit : Bool) (suffix : List Bool) :
    BoundedRun PA17TMRatArithmeticParse002.footerMachine (Tape.mk₂ left (bit :: suffix)) 1
      (Tape.mk₂ (bit :: left) suffix) 2 := by
  let state := PA17TMRatArithmeticParse002.cursorState
  refine ⟨[state 0 left (bit :: suffix), state 1 (bit :: left) suffix], ?_, by rfl⟩
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [state, List.isChain_cons_cons, TM0.step, PA17TMRatArithmeticParse002.footerMachine,
      PA17TMRatArithmeticParse002.cursorState, Tape.mk₂]
  · simp [TM0.step, PA17TMRatArithmeticParse002.footerMachine]

def counterForwardMachine : Machine 3 :=
  seqMachine outDyMachine PA17TMRatArithmeticParse002.footerMachine

theorem counterForward_bounded (archive digits suffix : List Bool) :
    BoundedRun counterForwardMachine
      (Tape.mk₂ (false :: archive) (PA17TMRatArithmeticCopy006.workspace digits ++ suffix)) 3
      (Tape.mk₂ (false :: copiedCounterLeft archive digits) suffix) (2 * digits.length + 4) := by
  have scan : BoundedRun outDyMachine
      (Tape.mk₂ (false :: archive) (PA17TMRatArithmeticCopy006.workspace digits ++ suffix)) 1
      (Tape.mk₂ (copiedCounterLeft archive digits) (false :: suffix)) (2 * digits.length + 2) :=
    by
      refine ⟨outDyTrace (false :: archive) digits suffix, ?_, by rw [outDyTrace_length]⟩
      simpa only [PA17TMRatArithmeticCopy006.workspace, PA17TMRatArithmeticWidth018.nxStream,
        outDyFinal, PA17TMRatArithmeticWidth018.scanState, pushField,
        copiedCounterLeft, PA17TMRatArithmeticCopy006.sourceLeft,
        List.append_assoc, List.cons_append, List.nil_append] using
          outDy_runsFrom (false :: archive) digits suffix
  exact (scan.seq (footer_any_bounded _ false suffix)).mono (by omega)

def counterFourForwardMachine : Machine 15 :=
  seqMachine (seqMachine (seqMachine counterForwardMachine counterForwardMachine)
    counterForwardMachine) counterForwardMachine

theorem counterFourForward_bounded (archive digits suffix : List Bool) :
    BoundedRun counterFourForwardMachine
      (Tape.mk₂ (false :: archive)
        (PA17TMRatArithmeticCopy006.workspace digits ++
          (PA17TMRatArithmeticCopy006.workspace digits ++
            (PA17TMRatArithmeticCopy006.workspace digits ++
              (PA17TMRatArithmeticCopy006.workspace digits ++ suffix))))) 15
      (Tape.mk₂ (false :: counterArchive archive digits 4) suffix) (8 * digits.length + 16) := by
  have actual := (((counterForward_bounded archive digits
    (PA17TMRatArithmeticCopy006.workspace digits ++
      (PA17TMRatArithmeticCopy006.workspace digits ++
        (PA17TMRatArithmeticCopy006.workspace digits ++ suffix)))).seq
    (counterForward_bounded (counterArchive archive digits 1) digits
      (PA17TMRatArithmeticCopy006.workspace digits ++
        (PA17TMRatArithmeticCopy006.workspace digits ++ suffix)))).seq
    (counterForward_bounded (counterArchive archive digits 2) digits
      (PA17TMRatArithmeticCopy006.workspace digits ++ suffix))).seq
    (counterForward_bounded (counterArchive archive digits 3) digits suffix)
  exact actual.mono (by omega)

def markedPowerWord (n : Nat) : Nat → Nat → List Bool
  | 0, gap => true :: (List.replicate gap false ++ [true])
  | depth + 1, gap => pairs true n ++ false :: false :: markedPowerWord n depth gap

def markGapStartMachine : Machine 17 :=
  seqMachine counterFourForwardMachine (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
def markGapMachine : Machine 49 := seqMachine markGapStartMachine counterFourBackMachine

theorem markGap_bounded (archive : List Bool) (n gap : Nat) :
    BoundedRun markGapMachine (Tape.mk₂ (false :: archive) (powerWord n 4 gap)) 49
      (Tape.mk₂ (false :: archive) (markedPowerWord n 4 gap)) (16 * n + 46) := by
  have forward := counterFourForward_bounded archive (List.replicate n false)
    (false :: (List.replicate gap false ++ [true]))
  have mark : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ (false :: counterArchive archive (List.replicate n false) 4)
        (false :: (List.replicate gap false ++ [true]))) 1
      (Tape.mk₂ (false :: counterArchive archive (List.replicate n false) 4)
        (true :: (List.replicate gap false ++ [true]))) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false true _ _,
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom false true _ _, by rfl⟩
  have back := counterFourBack_bounded archive (List.replicate n false)
    (true :: (List.replicate gap false ++ [true]))
  have actual := (forward.seq mark).seq back
  have exit : rightLabel (a := 17) (31 : Fin 32) = (49 : Fin 50) := by decide
  rw [exit] at actual
  simpa only [markGapMachine, markGapStartMachine, powerWord, markedPowerWord, pairs_true,
    PA17TMRatArithmeticCopy006.workspace, List.append_assoc, List.cons_append,
    List.nil_append, List.length_replicate] using actual.mono (by simp only [List.length_replicate]; omega :
      (8 * (List.replicate n false).length + 16) + 2 +
        (8 * (List.replicate n false).length + 28) ≤ 16 * n + 46)

def sourceSuffix (n gap : Nat) : List Bool := true :: false :: markedPowerWord n 4 gap

def returnOriginalMachine : Machine 80 :=
  seqMachine (seqMachine markGapMachine CountAppend.fromDestinationMachine) nxRoute.back

theorem returnOriginal_bounded (archive nx dx ny dy : List Bool) (n gap : Nat) :
    BoundedRun returnOriginalMachine
      (Tape.mk₂ (false :: PhysicalReserve.preservedArchive archive nx dx ny dy) (powerWord n 4 gap))
      (rightLabel (a := 53) nxRoute.backPort)
      (Tape.mk₂ (false :: archive)
        (fieldWord (nxContext dx ny dy) (false :: nx) (sourceSuffix n gap)))
      (16 * n + 2 * (false :: nx).length + TotalWidth.numCost dx ny dy + 50) := by
  have mark := markGap_bounded (PhysicalReserve.preservedArchive archive nx dx ny dy) n gap
  have fromCount := CountAppend.fromDestination_bounded (TotalWidth.bankLeft archive nx dx ny dy)
    (markedPowerWord n 4 gap)
  have original := (nx_route_correct dx ny dy).back_run archive (false :: nx) (sourceSuffix n gap)
  have actual := (mark.seq fromCount).seq original
  exact actual.mono (by unfold TotalWidth.numCost; omega)

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.MarshalAnchor
