module

public import Structure.RootB23_Threshold_Window_GapRoute_017

/-! Exact one/two/three-field navigation used by the second, third and
fourth payload copies. Existing flagged scans/rewinds perform every move;
the literal 0010 connectors and both suffix boundaries are retained. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadNav
open Turing PSTRTMSeq005
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticAllocatePass023

def nextLeft (left digits : List Bool) : List Bool := false :: true :: false :: pushField left digits
def word2 (a b suffix : List Bool) : List Bool :=
  PA17TMRatArithmeticCopy006.workspace a ++ true :: false :: (PA17TMRatArithmeticCopy006.workspace b ++ suffix)
def word3 (a b c suffix : List Bool) : List Bool :=
  PA17TMRatArithmeticCopy006.workspace a ++ true :: false :: word2 b c suffix

theorem scan_bounded (left digits suffix : List Bool) :
    BoundedRun outDyMachine
      (Tape.mk₂ left (PA17TMRatArithmeticCopy006.workspace digits ++ suffix)) 1
      (Tape.mk₂ (pushField left digits) (false :: suffix)) (2 * digits.length + 2) := by
  refine ⟨outDyTrace left digits suffix, ?_, by rw [outDyTrace_length]⟩
  simpa only [PA17TMRatArithmeticCopy006.workspace, PA17TMRatArithmeticWidth018.nxStream,
    outDyFinal, PA17TMRatArithmeticWidth018.scanState,
    List.append_assoc, List.cons_append, List.nil_append] using outDy_runsFrom left digits suffix

theorem rewind_bounded (archive digits suffix : List Bool) :
    BoundedRun PA17TMRatArithmeticParse002.fieldBackMachine
      (Tape.mk₂ (pushField (false :: archive) digits) (false :: suffix)) 5
      (Tape.mk₂ (false :: archive) (PA17TMRatArithmeticCopy006.workspace digits ++ suffix))
      (2 * digits.length + 5) := by
  refine ⟨PA17TMRatArithmeticParse002.fieldBackTrace archive digits (false :: suffix), ?_,
    by rw [PA17TMRatArithmeticParse002.fieldBackTrace_length]⟩
  have exit : rightLabel (a := 1) (3 : Fin 4) = (5 : Fin 6) := by decide
  simpa only [PA17TMRatArithmeticCopy006.workspace, pushField,
    PA17TMRatArithmeticParse002.fieldBackFinal, PSTRTMMulRewind085.state,
    rightCfg, exit, List.append_assoc, List.cons_append, List.nil_append] using
      PA17TMRatArithmeticParse002.fieldBack_runsFrom archive digits (false :: suffix)

def skip2Machine : Machine 7 := seqMachine (seqMachine outDyMachine GapRoute.toCounterMachine) outDyMachine
def skip3Machine : Machine 13 := seqMachine (seqMachine skip2Machine GapRoute.toCounterMachine) outDyMachine

theorem skip2_bounded (left a b suffix : List Bool) :
    BoundedRun skip2Machine (Tape.mk₂ left (word2 a b suffix)) 7
      (Tape.mk₂ (pushField (nextLeft left a) b) (false :: suffix))
      (2 * (a.length + b.length) + 8) := by
  have first := scan_bounded left a (true :: false :: (PA17TMRatArithmeticCopy006.workspace b ++ suffix))
  have connector := GapRoute.toCounter_bounded (pushField left a)
    (PA17TMRatArithmeticCopy006.workspace b ++ suffix)
  have second := scan_bounded (nextLeft left a) b suffix
  exact ((first.seq connector).seq second).mono (by omega)

theorem skip3_bounded (left a b c suffix : List Bool) :
    BoundedRun skip3Machine (Tape.mk₂ left (word3 a b c suffix)) 13
      (Tape.mk₂ (pushField (nextLeft (nextLeft left a) b) c) (false :: suffix))
      (2 * (a.length + b.length + c.length) + 14) := by
  have first := skip2_bounded left a b (true :: false :: (PA17TMRatArithmeticCopy006.workspace c ++ suffix))
  have connector := GapRoute.toCounter_bounded (pushField (nextLeft left a) b)
    (PA17TMRatArithmeticCopy006.workspace c ++ suffix)
  have last := scan_bounded (nextLeft (nextLeft left a) b) c suffix
  have actual := (first.seq connector).seq last
  exact actual.mono (by omega)

def back2Machine : Machine 15 :=
  seqMachine (seqMachine PA17TMRatArithmeticParse002.fieldBackMachine CountAppend.fromDestinationMachine)
    PA17TMRatArithmeticParse002.fieldBackMachine
def back3Machine : Machine 25 :=
  seqMachine (seqMachine back2Machine CountAppend.fromDestinationMachine)
    PA17TMRatArithmeticParse002.fieldBackMachine

theorem back2_bounded (archive a b suffix : List Bool) :
    BoundedRun back2Machine
      (Tape.mk₂ (pushField (nextLeft (false :: archive) a) b) (false :: suffix)) 15
      (Tape.mk₂ (false :: archive) (word2 a b suffix)) (2 * (a.length + b.length) + 14) := by
  have last := rewind_bounded (true :: false :: pushField (false :: archive) a) b suffix
  have connector := CountAppend.fromDestination_bounded (pushField (false :: archive) a)
    (PA17TMRatArithmeticCopy006.workspace b ++ suffix)
  have first := rewind_bounded archive a (true :: false :: (PA17TMRatArithmeticCopy006.workspace b ++ suffix))
  have actual := (last.seq connector).seq first
  exact actual.mono (by omega)

theorem back3_bounded (archive a b c suffix : List Bool) :
    BoundedRun back3Machine
      (Tape.mk₂ (pushField (nextLeft (nextLeft (false :: archive) a) b) c) (false :: suffix)) 25
      (Tape.mk₂ (false :: archive) (word3 a b c suffix))
      (2 * (a.length + b.length + c.length) + 23) := by
  have last := back2_bounded (true :: false :: pushField (false :: archive) a) b c suffix
  have connector := CountAppend.fromDestination_bounded (pushField (false :: archive) a) (word2 b c suffix)
  have first := rewind_bounded archive a (true :: false :: word2 b c suffix)
  have actual := (last.seq connector).seq first
  exact actual.mono (by omega)

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadNav
