module
public import Common.ROOT_TM_GCD_Parity_013

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDHalfResident014
open PaperProofs.Common.Native.RationalControllerComputation
local notation "cols" => PSTRTMBinaryAdd024.operandColumns
local notation "leftCols" => PSTRTMCompareCode054.leftColumns

/-- Marker-driven forward scan then the genuine high-to-low halver.
Every local HALT transfer is an actual write-self step, with no head reset. -/
def residentHalfMachine : Machine 52 :=
  PSTRTMSeq005.seqMachine ROOTTMGCDZero006.zeroMachine ROOTTMGCDHalf001.halfMachine
def initial (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) : MachineState 52 :=
  PSTRTMSeq005.leftCfg (b:=24) (ROOTTMGCDZero006.state (ROOTTMGCDZero006.aState 0)
    (false::archive) (cols pairs++false::false::suffix))
def final (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) : MachineState 52 :=
  PSTRTMSeq005.rightCfg (a:=27) (ROOTTMGCDHalf001.state
    (ROOTTMGCDHalf001.haltLabel (ROOTTMGCDHalf001.finalControl (ROOTTMGCDHalf001.carryControl false false) pairs.reverse))
    (false::archive) (cols (ROOTTMGCDHalf001.halfPairs pairs)++false::false::suffix))
def trace (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) : List (MachineState 52) :=
  (ROOTTMGCDZeroTrace007.zeroTrace 0 (false::archive) [] pairs suffix).map (PSTRTMSeq005.leftCfg (b:=24)) ++
    (ROOTTMGCDHalf001.fullTrace archive pairs.reverse (false::false::suffix)).map (PSTRTMSeq005.rightCfg (a:=27))

theorem residentHalf_runsFrom (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom residentHalfMachine (initial archive pairs suffix)
      (trace archive pairs suffix) (final archive pairs suffix) := by
  apply PSTRTMSeq005.seq_runsFrom ROOTTMGCDZero006.zeroMachine ROOTTMGCDHalf001.halfMachine
    (ROOTTMGCDZero006.state (ROOTTMGCDZero006.aState 0) (false::archive) (cols pairs++false::false::suffix))
    (ROOTTMGCDZero006.state (ROOTTMGCDZero006.haltLabel (ROOTTMGCDZero006.resultControl 0 pairs))
      (leftCols pairs.reverse++false::archive) (false::false::suffix))
    (ROOTTMGCDHalf001.state
      (ROOTTMGCDHalf001.haltLabel (ROOTTMGCDHalf001.finalControl (ROOTTMGCDHalf001.carryControl false false) pairs.reverse))
      (false::archive) (cols (ROOTTMGCDHalf001.halfPairs pairs)++false::false::suffix))
    (ROOTTMGCDZeroTrace007.zeroTrace 0 (false::archive) [] pairs suffix)
    (ROOTTMGCDHalf001.fullTrace archive pairs.reverse (false::false::suffix))
  · exact ROOTTMGCDZeroTrace007.zero_runsFrom 0 (false::archive) pairs suffix
  · exact ROOTTMGCDHalf001.half_runsFrom archive pairs (false::false::suffix)

theorem residentHalf_length (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (trace archive pairs suffix).length=9*pairs.length+6 := by
  unfold trace
  rw [List.length_append,List.length_map,List.length_map,ROOTTMGCDZeroTrace007.zero_length,
    ROOTTMGCDHalf001.full_length,List.length_reverse]
  omega
theorem residentHalf_final_tape (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (final archive pairs suffix).Tape=Turing.Tape.mk₂ (false::archive)
      (cols (ROOTTMGCDHalf001.halfPairs pairs)++false::false::suffix) := rfl
theorem residentHalf_visitedSpace_le (archive : List Bool) (pairs : List (Bool × Bool))
    (suffix : List Bool) (inputLength : Nat) :
    visitedSpace residentHalfMachine inputLength (trace archive pairs suffix) ≤ inputLength+18*pairs.length+13 := by
  have h:=PSTRTMTrace002.visitedSpace_le residentHalfMachine inputLength (trace archive pairs suffix)
  rw [residentHalf_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDHalfResident014
