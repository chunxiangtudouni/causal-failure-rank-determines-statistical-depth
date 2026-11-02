module

public import Structure.RootB23_Threshold_Window_CounterData_009
public import Structure.RootB23_Threshold_Window_QuarticCost_008
public import Structure.RootB23_Threshold_RoutedLoop_007

/-! Three real nearest-field copies turn ONE actually copied width field
into four equal physical counters. The old counter, all its data and the
entire WEST archive are retained. Every temporary footer is cleared before
advancing; the resulting four fields have precisely the powerWord layout. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

open Turing PSTRTMSeq005
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticAllocate013 (setMarkerMachine setMarkerTrace setMarker_runsFrom)
open PA17TMRatArithmeticAllocatePass023 (outDyMachine outDyTrace outDy_runsFrom outDyTrace_length)
open PA17TMRatArithmeticParse002 (footerMachine footerTrace footer_runsFrom
  backOneMachine backOneTrace backOne_runsFrom fieldBackMachine fieldBackTrace
  fieldBack_runsFrom fieldBackTrace_length)

def copiedCounterLeft (archive digits : List Bool) : List Bool :=
  PA17TMRatArithmeticCopy006.sourceLeft archive digits

def counterCopyStartMachine : Machine 3 := seqMachine outDyMachine (setMarkerMachine true)
def counterCopyBodyMachine : Machine 46 :=
  seqMachine counterCopyStartMachine PA17TMRatArithmeticCopy006.copyMachine
def counterCopyClearMachine : Machine 48 := seqMachine counterCopyBodyMachine (setMarkerMachine false)
def counterCopyMachine : Machine 50 := seqMachine counterCopyClearMachine footerMachine

theorem counterCopy_bounded (archive digits : List Bool) :
    BoundedRun counterCopyMachine
      (Tape.mk₂ (false :: archive) (PA17TMRatArithmeticCopy006.workspace digits)) 50
      (Tape.mk₂ (false :: copiedCounterLeft archive digits)
        (PA17TMRatArithmeticCopy006.workspace digits))
      (4 * digits.length ^ 2 + 22 * digits.length + 21) := by
  have scan : BoundedRun outDyMachine
      (Tape.mk₂ (false :: archive) (PA17TMRatArithmeticCopy006.workspace digits)) 1
      (Tape.mk₂ (copiedCounterLeft archive digits) [false]) (2 * digits.length + 2) := by
    exact ⟨outDyTrace (false :: archive) digits [], outDy_runsFrom (false :: archive) digits [],
      by rw [outDyTrace_length]⟩
  have mark : BoundedRun (setMarkerMachine true)
      (Tape.mk₂ (copiedCounterLeft archive digits) [false]) 1
      (Tape.mk₂ (copiedCounterLeft archive digits) [true]) 2 :=
    ⟨setMarkerTrace false true _ [], setMarker_runsFrom false true _ [], by rfl⟩
  have copy : BoundedRun PA17TMRatArithmeticCopy006.copyMachine
      (Tape.mk₂ (copiedCounterLeft archive digits) [true]) 42
      (Tape.mk₂ (copiedCounterLeft archive digits)
        (true :: PA17TMRatArithmeticCopy006.workspace digits))
      (4 * digits.length ^ 2 + 20 * digits.length + 13) :=
    ⟨PA17TMRatArithmeticCopy006.copyTrace archive digits,
      PA17TMRatArithmeticCopy006.copy_runsFrom archive digits,
      by rw [PA17TMRatArithmeticCopy006.copy_length]⟩
  have clear : BoundedRun (setMarkerMachine false)
      (Tape.mk₂ (copiedCounterLeft archive digits)
        (true :: PA17TMRatArithmeticCopy006.workspace digits)) 1
      (Tape.mk₂ (copiedCounterLeft archive digits)
        (false :: PA17TMRatArithmeticCopy006.workspace digits)) 2 :=
    ⟨setMarkerTrace true false _ _, setMarker_runsFrom true false _ _, by rfl⟩
  have advance : BoundedRun footerMachine
      (Tape.mk₂ (copiedCounterLeft archive digits)
        (false :: PA17TMRatArithmeticCopy006.workspace digits)) 1
      (Tape.mk₂ (false :: copiedCounterLeft archive digits)
        (PA17TMRatArithmeticCopy006.workspace digits)) 2 := by
    refine ⟨[PA17TMRatArithmeticParse002.cursorState 0 (copiedCounterLeft archive digits)
      (false :: PA17TMRatArithmeticCopy006.workspace digits),
      PA17TMRatArithmeticParse002.cursorState 1 (false :: copiedCounterLeft archive digits)
      (PA17TMRatArithmeticCopy006.workspace digits)], ?_, by rfl⟩
    refine ⟨rfl, ?_, rfl, ?_⟩
    · simp [List.isChain_cons_cons, TM0.step, footerMachine,
        PA17TMRatArithmeticParse002.cursorState, Tape.mk₂]
    · simp [TM0.step, footerMachine]
  exact ((((scan.seq mark).seq copy).seq clear).seq advance).mono (by omega)

def counterBackMachine : Machine 7 := seqMachine backOneMachine fieldBackMachine

theorem counterBack_bounded (archive digits suffix : List Bool) :
    BoundedRun counterBackMachine
      (Tape.mk₂ (false :: copiedCounterLeft archive digits) suffix) 7
      (Tape.mk₂ (false :: archive) (PA17TMRatArithmeticCopy006.workspace digits ++ suffix))
      (2 * digits.length + 7) := by
  have back : BoundedRun backOneMachine
      (Tape.mk₂ (false :: copiedCounterLeft archive digits) suffix) 1
      (Tape.mk₂ (copiedCounterLeft archive digits) (false :: suffix)) 2 :=
    ⟨backOneTrace _ false suffix, backOne_runsFrom _ false suffix, by rfl⟩
  have field : BoundedRun fieldBackMachine
      (Tape.mk₂ (copiedCounterLeft archive digits) (false :: suffix)) 5
      (Tape.mk₂ (false :: archive)
        (PA17TMRatArithmeticCopy006.workspace digits ++ suffix)) (2 * digits.length + 5) :=
    by
      refine ⟨fieldBackTrace archive digits (false :: suffix), ?_, by rw [fieldBackTrace_length]⟩
      have exit : rightLabel (a := 1) (3 : Fin 4) = (5 : Fin 6) := by decide
      simpa only [copiedCounterLeft, PA17TMRatArithmeticCopy006.sourceLeft,
        PA17TMRatArithmeticCopy006.workspace, PA17TMRatArithmeticParse002.fieldBackFinal,
        PSTRTMMulRewind085.state, rightCfg, exit, List.append_assoc, List.cons_append,
        List.nil_append] using fieldBack_runsFrom archive digits (false :: suffix)
  exact (back.seq field).mono (by omega)

def counterThreeMachine : Machine 152 :=
  seqMachine (seqMachine counterCopyMachine counterCopyMachine) counterCopyMachine

def counterArchive (archive digits : List Bool) : Nat → List Bool
  | 0 => archive
  | later + 1 => copiedCounterLeft (counterArchive archive digits later) digits

theorem counterThree_bounded (archive digits : List Bool) :
    BoundedRun counterThreeMachine
      (Tape.mk₂ (false :: archive) (PA17TMRatArithmeticCopy006.workspace digits)) 152
      (Tape.mk₂ (false :: counterArchive archive digits 3)
        (PA17TMRatArithmeticCopy006.workspace digits))
      (12 * digits.length ^ 2 + 66 * digits.length + 63) := by
  have actual := ((counterCopy_bounded archive digits).seq
    (counterCopy_bounded (counterArchive archive digits 1) digits)).seq
      (counterCopy_bounded (counterArchive archive digits 2) digits)
  exact actual.mono (by omega)

def counterFarMachine : Machine 4 := fun q _ =>
  match q.val with
  | 0 => some (1, .move .right)
  | 1 => some (2, .move .right)
  | 2 => some (3, .write true)
  | 3 => some (4, .move .left)
  | _ => none

theorem counterFar_bounded (left : List Bool) :
    BoundedRun counterFarMachine (Tape.mk₂ left [false, false, false]) 4
      (Tape.mk₂ (false :: left) [false, true]) 5 := by
  let state := fun (q : Fin 5) (west east : List Bool) =>
    (⟨q, Tape.mk₂ west east⟩ : MachineState 4)
  refine ⟨[state 0 left [false,false,false], state 1 (false::left) [false,false],
    state 2 (false::false::left) [false], state 3 (false::false::left) [true],
    state 4 (false::left) [false,true]], ?_, by rfl⟩
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [state, List.isChain_cons_cons, TM0.step, counterFarMachine, Tape.mk₂]
  · simp [TM0.step, counterFarMachine]

def counterFourBackMachine : Machine 31 :=
  seqMachine (seqMachine (seqMachine counterBackMachine counterBackMachine) counterBackMachine)
    counterBackMachine

theorem counterFourBack_bounded (archive digits suffix : List Bool) :
    BoundedRun counterFourBackMachine
      (Tape.mk₂ (false :: counterArchive archive digits 4) suffix) 31
      (Tape.mk₂ (false :: archive)
        (PA17TMRatArithmeticCopy006.workspace digits ++
          PA17TMRatArithmeticCopy006.workspace digits ++
          PA17TMRatArithmeticCopy006.workspace digits ++
          PA17TMRatArithmeticCopy006.workspace digits ++ suffix))
      (8 * digits.length + 28) := by
  have actual := (((counterBack_bounded (counterArchive archive digits 3) digits suffix).seq
    (counterBack_bounded (counterArchive archive digits 2) digits
      (PA17TMRatArithmeticCopy006.workspace digits ++ suffix))).seq
    (counterBack_bounded (counterArchive archive digits 1) digits
      (PA17TMRatArithmeticCopy006.workspace digits ++
        (PA17TMRatArithmeticCopy006.workspace digits ++ suffix)))).seq
    (counterBack_bounded archive digits
      (PA17TMRatArithmeticCopy006.workspace digits ++
        (PA17TMRatArithmeticCopy006.workspace digits ++
          (PA17TMRatArithmeticCopy006.workspace digits ++ suffix))))
  have exit : rightLabel (a := 23) (7 : Fin 8) = (31 : Fin 32) := by decide
  rw [exit] at actual
  simpa only [List.append_assoc, counterFourBackMachine, counterArchive] using actual.mono (by omega :
    (2 * digits.length + 7 + (2 * digits.length + 7) + (2 * digits.length + 7)) +
      (2 * digits.length + 7) ≤ 8 * digits.length + 28)

def counterFinishMachine : Machine 38 :=
  seqMachine (seqMachine outDyMachine counterFarMachine) counterFourBackMachine

theorem counterFinish_bounded (archive digits : List Bool) :
    BoundedRun counterFinishMachine
      (Tape.mk₂ (false :: counterArchive archive digits 3)
        (PA17TMRatArithmeticCopy006.workspace digits)) 38
      (Tape.mk₂ (false :: archive)
        (PA17TMRatArithmeticCopy006.workspace digits ++
          PA17TMRatArithmeticCopy006.workspace digits ++
          PA17TMRatArithmeticCopy006.workspace digits ++
          PA17TMRatArithmeticCopy006.workspace digits ++ [false,true]))
      (10 * digits.length + 35) := by
  have scan : BoundedRun outDyMachine
      (Tape.mk₂ (false :: counterArchive archive digits 3)
        (PA17TMRatArithmeticCopy006.workspace digits)) 1
      (Tape.mk₂ (counterArchive archive digits 4) [false]) (2 * digits.length + 2) :=
    ⟨outDyTrace _ digits [], outDy_runsFrom _ digits [], by rw [outDyTrace_length]⟩
  have far := counterFar_bounded (counterArchive archive digits 4)
  have blank : Tape.mk₂ (counterArchive archive digits 4) [false,false,false] =
      Tape.mk₂ (counterArchive archive digits 4) [false] := by
    apply congrArg (Tape.mk' (ListBlank.mk (counterArchive archive digits 4)))
    exact (PSTRTMRawNat010.blank_append_false [false,false]).trans
      (PSTRTMRawNat010.blank_append_false [false])
  rw [blank] at far
  exact ((scan.seq far).seq (counterFourBack_bounded archive digits [false,true])).mono (by omega)

def fourCounterMachine : Machine 191 := seqMachine counterThreeMachine counterFinishMachine

theorem fourCounter_bounded (archive : List Bool) (n : Nat) :
    BoundedRun fourCounterMachine
      (Tape.mk₂ (false :: archive) (PA17TMRatArithmeticCopy006.workspace (List.replicate n false))) 191
      (Tape.mk₂ (false :: archive) (powerWord n 4 0)) (12 * n ^ 2 + 76 * n + 98) := by
  have actual := (counterThree_bounded archive (List.replicate n false)).seq
    (counterFinish_bounded archive (List.replicate n false))
  have exit : rightLabel (a := 152) (38 : Fin 39) = (191 : Fin 192) := by decide
  rw [exit] at actual
  simpa only [fourCounterMachine, powerWord, pairs_true, PA17TMRatArithmeticCopy006.workspace,
    List.append_assoc, List.cons_append, List.nil_append, List.replicate_zero, List.length_replicate]
      using actual.mono (by simp only [List.length_replicate]; omega :
        (12 * (List.replicate n false).length ^ 2 + 66 * (List.replicate n false).length + 63) +
          (10 * (List.replicate n false).length + 35) ≤ 12 * n ^ 2 + 76 * n + 98)

def prepareFourCounterMachine : Machine 200 := seqMachine normalizeCounterMachine fourCounterMachine

theorem prepareFourCounter_bounded (archive digits : List Bool) :
    BoundedRun prepareFourCounterMachine
      (Tape.mk₂ (false :: archive) (PA17TMRatArithmeticCopy006.workspace digits)) 200
      (Tape.mk₂ (false :: archive) (powerWord digits.length 4 0))
      (12 * digits.length ^ 2 + 82 * digits.length + 105) := by
  have normalized : BoundedRun normalizeCounterMachine
      (Tape.mk₂ (false :: archive) (PA17TMRatArithmeticCopy006.workspace digits)) 8
      (Tape.mk₂ (false :: archive)
        (PA17TMRatArithmeticCopy006.workspace (List.replicate digits.length false)))
      (6 * digits.length + 7) := by
    refine ⟨normalizeCounterTrace archive [] digits, ?_, ?_⟩
    · have exit : rightLabel (a := 3) (4 : Fin 5) = (8 : Fin 9) := by decide
      simpa only [PA17TMRatArithmeticCopy006.workspace, pairs_true, rightCfg, exit,
        homeState] using normalizeCounter_runsFrom archive [] digits
    · rw [normalizeCounter_length]
  exact (normalized.seq (fourCounter_bounded archive digits.length)).mono (by omega)

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
