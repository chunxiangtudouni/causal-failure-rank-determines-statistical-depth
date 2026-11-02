module

public import Structure.RootB23_Threshold_Window_GapRoute_017

/-! Actually create the first far payload anchor in the original blank EAST
tail, retain both allocated-gap anchors, and return to the original NUM.
The caller's arbitrary WEST archive is carried through every move. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadInit
open Turing PSTRTMSeq005
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticAllocate013

theorem tape_three_false (left word : List Bool) :
    Tape.mk₂ left (word ++ [false,false,false]) = Tape.mk₂ left word := by
  have first := PA17TMRatArithmeticBankCopy024.tape_append_false left word
  have second := PA17TMRatArithmeticBankCopy024.tape_append_false left (word ++ [false])
  have third := PA17TMRatArithmeticBankCopy024.tape_append_false left ((word ++ [false]) ++ [false])
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using (third.trans second).trans first

def anchorMachine : Machine 5 := fun q _ =>
  match q.val with
  | 0 => some (1, .move .right)
  | 1 => some (2, .move .right)
  | 2 => some (3, .write true)
  | 3 => some (4, .move .left)
  | 4 => some (5, .move .left)
  | _ => none

theorem anchor_bounded (left : List Bool) :
    BoundedRun anchorMachine (Tape.mk₂ left [true]) 5
      (Tape.mk₂ left [true,false,true,false,false,false]) 6 := by
  let state := fun (q : Fin 6) (west east : List Bool) => (⟨q, Tape.mk₂ west east⟩ : MachineState 5)
  have actual : BoundedRun anchorMachine (Tape.mk₂ left [true]) 5
      (Tape.mk₂ left [true,false,true]) 6 := by
    refine ⟨[state 0 left [true], state 1 (true::left) [], state 2 (false::true::left) [],
      state 3 (false::true::left) [true], state 4 (true::left) [false,true],
      state 5 left [true,false,true]], ?_, by rfl⟩
    refine ⟨rfl, ?_, rfl, ?_⟩
    · simp [state, List.isChain_cons_cons, TM0.step, anchorMachine, Tape.mk₂]
    · simp [TM0.step, anchorMachine]
  have padding := tape_three_false left [true,false,true]
  change Tape.mk₂ left [true,false,true,false,false,false] = Tape.mk₂ left [true,false,true] at padding
  rw [padding]
  exact actual

def forwardMachine : Machine 65 :=
  seqMachine MarshalAnchor.markGapMachine MarshalAnchor.counterFourForwardMachine
def crossMachine : Machine 67 := seqMachine forwardMachine (gapSeekMachine .right)
def anchoredMachine : Machine 73 := seqMachine crossMachine anchorMachine
def backGapMachine : Machine 75 := seqMachine anchoredMachine (gapSeekMachine .left)
def backCountersMachine : Machine 107 := seqMachine backGapMachine counterFourBackMachine
def backFooterMachine : Machine 111 := seqMachine backCountersMachine CountAppend.fromDestinationMachine
def machine : Machine 138 := seqMachine backFooterMachine nxRoute.back

theorem init_bounded (archive nx dx ny dy : List Bool) (n gap : Nat) :
    BoundedRun machine
      (Tape.mk₂ (false :: PhysicalReserve.preservedArchive archive nx dx ny dy) (powerWord n 4 gap))
      (rightLabel (a := 111) nxRoute.backPort)
      (Tape.mk₂ (false :: archive)
        (fieldWord (GapRoute.context (nxContext dx ny dy) n gap) (false :: nx) (workSuffix 0 [])))
      (32 * n + 2 * gap + 2 * (false :: nx).length + TotalWidth.numCost dx ny dy + 104) := by
  let footer := TotalWidth.bankLeft archive nx dx ny dy
  let countArchive := PhysicalReserve.preservedArchive archive nx dx ny dy
  let counterLeft := false :: counterArchive countArchive (List.replicate n false) 4
  let east := [false,true,false,false,false]
  let word := GapRoute.counterWords n ++ true :: (List.replicate gap false ++ true :: east)
  let tail := true :: false :: word
  have mark := MarshalAnchor.markGap_bounded countArchive n gap
  have fields := MarshalAnchor.counterFourForward_bounded countArchive (List.replicate n false)
    (true :: (List.replicate gap false ++ [true]))
  have cross : BoundedRun (gapSeekMachine .right)
      (Tape.mk₂ counterLeft (true :: (List.replicate gap false ++ [true]))) 1
      (Tape.mk₂ (List.replicate gap false ++ true :: counterLeft) [true]) (gap + 2) :=
    ⟨PA17TMRatArithmeticRecordNav032.gapRightTrace gap counterLeft true [],
      PA17TMRatArithmeticRecordNav032.gapRight_runsFrom gap counterLeft true [],
      by rw [PA17TMRatArithmeticRecordNav032.gapRightTrace_length]⟩
  have anchor := anchor_bounded (List.replicate gap false ++ true :: counterLeft)
  have back : BoundedRun (gapSeekMachine .left)
      (Tape.mk₂ (List.replicate gap false ++ true :: counterLeft) (true :: east)) 1
      (Tape.mk₂ counterLeft (true :: (List.replicate gap false ++ true :: east))) (gap + 2) :=
    ⟨returnGapTrace gap counterLeft east, returnGap_runsFrom gap counterLeft east,
      by rw [returnGap_length]⟩
  have counters := counterFourBack_bounded countArchive (List.replicate n false)
    (true :: (List.replicate gap false ++ true :: east))
  have fromCount := CountAppend.fromDestination_bounded footer word
  have original := (nx_route_correct dx ny dy).back_run archive (false :: nx) tail
  dsimp only [footer, countArchive, counterLeft, east, word, tail]
    at mark fields cross anchor back counters fromCount original
  simp only [MarshalAnchor.markedPowerWord, pairs_true, powerWord,
    PA17TMRatArithmeticCopy006.workspace, GapRoute.counterWords,
    RootB23.Threshold.RoutedCopy.destinationLeft, List.replicate_zero,
    PhysicalReserve.preservedArchive, List.append_assoc, List.cons_append, List.nil_append]
    at mark fields cross anchor back counters fromCount original
  have actual := ((((((mark.seq fields).seq cross).seq anchor).seq back).seq counters).seq fromCount).seq original
  have emptyBlocks : PSTRTMIncrement009.blocks [] = [] := rfl
  simpa only [machine, backFooterMachine, backCountersMachine, backGapMachine, anchoredMachine,
    crossMachine, forwardMachine, GapRoute.context, fieldWord, nxContext, dxContext,
    PA17TMRatArithmeticWidth018.nxStream, workSuffix, GapRoute.counterWords,
    PA17TMRatArithmeticCopy006.workspace, PhysicalReserve.preservedArchive, powerWord, pairs_true,
    TotalWidth.bankLeft, emptyBlocks, List.replicate_zero, List.append_assoc, List.cons_append, List.nil_append]
    using actual.mono (by simp only [List.length_replicate]; unfold TotalWidth.numCost; omega :
      ((((((16 * n + 46 + (8 * (List.replicate n false).length + 16)) + (gap + 2)) + 6) +
        (gap + 2)) + (8 * (List.replicate n false).length + 28)) + 4) +
        (2 * (false :: nx).length + (2 * ((false :: dx).length + (false :: ny).length +
          (false :: dy).length) + 23)) ≤
          32 * n + 2 * gap + 2 * (false :: nx).length + TotalWidth.numCost dx ny dy + 104)

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadInit
