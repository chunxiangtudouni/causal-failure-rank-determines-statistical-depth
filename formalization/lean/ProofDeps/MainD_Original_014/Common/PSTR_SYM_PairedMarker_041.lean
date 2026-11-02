module

public import Common.PSTR_SYM_PairedDatum_040

/-! Real marker installation and restoration with three saved Bool cells.
All control labels belong to fixed finite programs before the tape is given.
These two contracts do not yet provide the intervening root/cursor scans. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedCursor

open Turing PSTRTMSeq005

def savedCode (tag first second : Bool) : Nat :=
  (if tag then 4 else 0) + (if first then 2 else 0) + (if second then 1 else 0)

def savedTag (number : Nat) : Bool := decide (4 ≤ number % 8)
def savedFirst (number : Nat) : Bool := decide (2 ≤ number % 4)
def savedSecond (number : Nat) : Bool := decide (number % 2 = 1)

def markLabel (phase : Fin 10) (tag first second : Bool) : Fin 80 :=
  ⟨8 * phase.val + savedCode tag first second, by
    cases tag <;> cases first <;> cases second <;> simp [savedCode] <;> omega⟩

def restoreLabel (phase : Fin 16) (tag first second : Bool) : Fin 128 :=
  ⟨8 * phase.val + savedCode tag first second, by
    cases tag <;> cases first <;> cases second <;> simp [savedCode] <;> omega⟩

def markNext (label : Fin 80) (phase : Fin 10) : Fin 80 :=
  markLabel phase (savedTag label.val) (savedFirst label.val) (savedSecond label.val)

def restoreNext (label : Fin 128) (phase : Fin 16) : Fin 128 :=
  restoreLabel phase (savedTag label.val) (savedFirst label.val) (savedSecond label.val)

def markerSetupMachine : Machine 79 := fun label symbol =>
  match label.val / 8 with
  | 0 => some (markLabel 1 symbol false false, .write true)
  | 1 => some (markNext label 2, .move .left)
  | 2 => some (markNext label 3, .move .left)
  | 3 => some (markNext label 4, .move .left)
  | 4 => some (markNext label 5, .move .left)
  | 5 => some (markLabel 6 (savedTag label.val) symbol false, .write true)
  | 6 => some (markNext label 7, .move .left)
  | 7 => some (markNext label 8, .move .left)
  | 8 => some (markLabel 9 (savedTag label.val) (savedFirst label.val) symbol, .write false)
  | _ => none

def markerRestoreMachine : Machine 127 := fun label _ =>
  match label.val / 8 with
  | 0 => some (restoreNext label 1, .write (savedTag label.val))
  | 1 => some (restoreNext label 2, .move .left)
  | 2 => some (restoreNext label 3, .move .left)
  | 3 => some (restoreNext label 4, .move .left)
  | 4 => some (restoreNext label 5, .move .left)
  | 5 => some (restoreNext label 6, .write (savedFirst label.val))
  | 6 => some (restoreNext label 7, .move .left)
  | 7 => some (restoreNext label 8, .move .left)
  | 8 => some (restoreNext label 9, .write (savedSecond label.val))
  | 9 => some (restoreNext label 10, .move .right)
  | 10 => some (restoreNext label 11, .move .right)
  | 11 => some (restoreNext label 12, .move .right)
  | 12 => some (restoreNext label 13, .move .right)
  | 13 => some (restoreNext label 14, .move .right)
  | 14 => some (restoreNext label 15, .move .right)
  | _ => none

def markState (phase : Fin 10) (tag first second : Bool) (left right : List Bool) : MachineState 79 :=
  ⟨markLabel phase tag first second,Tape.mk₂ left right⟩

def restoreState (phase : Fin 16) (tag first second : Bool) (left right : List Bool) : MachineState 127 :=
  ⟨restoreLabel phase tag first second,Tape.mk₂ left right⟩

def markerTrace (near middle first far second : Bool) (archive : List Bool)
    (tag : Bool) (suffix : List Bool) : List (MachineState 79) :=
  [markState 0 false false false (near :: true :: middle :: first :: far :: second :: archive) (tag :: suffix),
    markState 1 tag false false (near :: true :: middle :: first :: far :: second :: archive) (true :: suffix),
    markState 2 tag false false (true :: middle :: first :: far :: second :: archive) (near :: true :: suffix),
    markState 3 tag false false (middle :: first :: far :: second :: archive) (true :: near :: true :: suffix),
    markState 4 tag false false (first :: far :: second :: archive) (middle :: true :: near :: true :: suffix),
    markState 5 tag false false (far :: second :: archive) (first :: middle :: true :: near :: true :: suffix),
    markState 6 tag first false (far :: second :: archive) (true :: middle :: true :: near :: true :: suffix),
    markState 7 tag first false (second :: archive) (far :: true :: middle :: true :: near :: true :: suffix),
    markState 8 tag first false archive (second :: far :: true :: middle :: true :: near :: true :: suffix),
    markState 9 tag first second archive (false :: far :: true :: middle :: true :: near :: true :: suffix)]

theorem marker_runsFrom (near middle first far second : Bool) (archive : List Bool)
    (tag : Bool) (suffix : List Bool) :
    RunsFrom markerSetupMachine
      ⟨0,Tape.mk₂ (near :: true :: middle :: first :: far :: second :: archive) (tag :: suffix)⟩
      (markerTrace near middle first far second archive tag suffix)
      (markState 9 tag first second archive
        (false :: far :: true :: middle :: true :: near :: true :: suffix)) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · cases tag <;> cases first <;> cases second <;>
      simp [markerTrace, List.isChain_cons_cons, TM0.step, markerSetupMachine,
        markState, markLabel, markNext, savedCode, savedTag, savedFirst, savedSecond, Tape.mk₂]
  · cases tag <;> cases first <;> cases second <;>
      simp [TM0.step, markerSetupMachine, markState, markLabel, savedCode]

theorem marker_length (near middle first far second : Bool) (archive : List Bool)
    (tag : Bool) (suffix : List Bool) :
    (markerTrace near middle first far second archive tag suffix).length = 10 := rfl

def restoreTrace (near middle first far second : Bool) (archive : List Bool)
    (tag : Bool) (suffix : List Bool) : List (MachineState 127) :=
  [restoreState 0 tag first second (near :: true :: middle :: true :: far :: false :: archive) (true :: suffix),
    restoreState 1 tag first second (near :: true :: middle :: true :: far :: false :: archive) (tag :: suffix),
    restoreState 2 tag first second (true :: middle :: true :: far :: false :: archive) (near :: tag :: suffix),
    restoreState 3 tag first second (middle :: true :: far :: false :: archive) (true :: near :: tag :: suffix),
    restoreState 4 tag first second (true :: far :: false :: archive) (middle :: true :: near :: tag :: suffix),
    restoreState 5 tag first second (far :: false :: archive) (true :: middle :: true :: near :: tag :: suffix),
    restoreState 6 tag first second (far :: false :: archive) (first :: middle :: true :: near :: tag :: suffix),
    restoreState 7 tag first second (false :: archive) (far :: first :: middle :: true :: near :: tag :: suffix),
    restoreState 8 tag first second archive (false :: far :: first :: middle :: true :: near :: tag :: suffix),
    restoreState 9 tag first second archive (second :: far :: first :: middle :: true :: near :: tag :: suffix),
    restoreState 10 tag first second (second :: archive) (far :: first :: middle :: true :: near :: tag :: suffix),
    restoreState 11 tag first second (far :: second :: archive) (first :: middle :: true :: near :: tag :: suffix),
    restoreState 12 tag first second (first :: far :: second :: archive) (middle :: true :: near :: tag :: suffix),
    restoreState 13 tag first second (middle :: first :: far :: second :: archive) (true :: near :: tag :: suffix),
    restoreState 14 tag first second (true :: middle :: first :: far :: second :: archive) (near :: tag :: suffix),
    restoreState 15 tag first second (near :: true :: middle :: first :: far :: second :: archive) (tag :: suffix)]

theorem restore_runsFrom (near middle first far second : Bool) (archive : List Bool)
    (tag : Bool) (suffix : List Bool) :
    RunsFrom markerRestoreMachine
      (restoreState 0 tag first second (near :: true :: middle :: true :: far :: false :: archive) (true :: suffix))
      (restoreTrace near middle first far second archive tag suffix)
      (restoreState 15 tag first second (near :: true :: middle :: first :: far :: second :: archive) (tag :: suffix)) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · cases tag <;> cases first <;> cases second <;>
      simp [restoreTrace, List.isChain_cons_cons, TM0.step, markerRestoreMachine,
        restoreState, restoreLabel, restoreNext, savedCode, savedTag, savedFirst, savedSecond, Tape.mk₂]
  · cases tag <;> cases first <;> cases second <;>
      simp [TM0.step, markerRestoreMachine, restoreState, restoreLabel, savedCode]

theorem restore_length (near middle first far second : Bool) (archive : List Bool)
    (tag : Bool) (suffix : List Bool) :
    (restoreTrace near middle first far second archive tag suffix).length = 16 := rfl

theorem marker_prefix_space (near middle first far second : Bool) (archive : List Bool)
    (tag : Bool) (suffix : List Bool) (inputLength clock : Nat) :
    visitedSpace markerSetupMachine inputLength
      ((markerTrace near middle first far second archive tag suffix).take clock) ≤ inputLength + 21 := by
  have cells := PSTRTMTrace002.visitedSpace_le markerSetupMachine inputLength
    ((markerTrace near middle first far second archive tag suffix).take clock)
  have count : ((markerTrace near middle first far second archive tag suffix).take clock).length ≤ 10 := by
    simp only [List.length_take, marker_length]
    omega
  omega

theorem restore_prefix_space (near middle first far second : Bool) (archive : List Bool)
    (tag : Bool) (suffix : List Bool) (inputLength clock : Nat) :
    visitedSpace markerRestoreMachine inputLength
      ((restoreTrace near middle first far second archive tag suffix).take clock) ≤ inputLength + 33 := by
  have cells := PSTRTMTrace002.visitedSpace_le markerRestoreMachine inputLength
    ((restoreTrace near middle first far second archive tag suffix).take clock)
  have count : ((restoreTrace near middle first far second archive tag suffix).take clock).length ≤ 16 := by
    simp only [List.length_take, restore_length]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedCursor
