module
public import Common.ROOT_TM_GCD_ZeroValue_008
public import Structure.PA17_TM_Division_Compose_006a

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDZeroResident010
open PaperProofs.Common.Native.RationalControllerComputation
open ROOTTMGCDZero006
open PA17TMDivisionCompose006
local notation "cols" => PSTRTMBinaryAdd024.operandColumns
local notation "leftCols" => PSTRTMCompareCode054.leftColumns

def rewindPhase (r : Fin 4) : Fin 5 := ⟨1+r.val,by have h:=r.isLt; omega⟩
def family (phase : Fin 5) : Machine 27 :=
  if phase.val=0 then zeroMachine else padMachine (by decide : 5 ≤ 27) PSTRTMColumnRewind067.rewindMachine
def ports (phase : Fin 5) (q : Fin 28) : Option (Fin 5 × Fin 28) :=
  if _h : phase.val=0 ∧ 24 ≤ q.val then some (⟨q.val-23,by have hq:=q.isLt; omega⟩,0) else none

/-- All four control-preserving rewind copies are fixed before operands.
Actual scan HALT control selects the copy through a charged write-self port. -/
def residentZeroMachine : Machine 139 := blockMachine family ports

theorem family_zero : family 0=zeroMachine := rfl
theorem family_rewind (r : Fin 4) : family (rewindPhase r)=
    padMachine (by decide : 5 ≤ 27) PSTRTMColumnRewind067.rewindMachine := by
  simp [family,rewindPhase]
theorem scan_port (r : Fin 4) : ports 0 (haltLabel r)=some (rewindPhase r,0) := by
  have hr:=r.isLt
  simp only [ports,Fin.val_zero,haltLabel,show 24 ≤ 24+r.val by omega,and_self,↓reduceDIte]
  congr 2
  apply Fin.ext
  simp only [rewindPhase]
  omega
theorem rewind_port_none (r : Fin 4) (q : Fin 28) : ports (rewindPhase r) q=none := by
  simp [ports,rewindPhase]

def initial (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) : MachineState 139 :=
  blockCfg (s:=27) (0 : Fin 5) (state (aState 0) (false::archive) (cols pairs++false::false::suffix))
def final (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) : MachineState 139 :=
  blockCfg (rewindPhase (resultControl 0 pairs)) (padCfg (by decide : 5 ≤ 27)
    (PSTRTMColumnRewind067.state 5 (false::archive) (cols pairs++false::false::suffix)))
def trace (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) : List (MachineState 139) :=
  (ROOTTMGCDZeroTrace007.zeroTrace 0 (false::archive) [] pairs suffix).map (blockCfg (s:=27) (0 : Fin 5)) ++
    ((PSTRTMColumnRewind067.fullTrace archive pairs.reverse (false::false::suffix)).map
      (padCfg (by decide : 5 ≤ 27))).map (blockCfg (s:=27) (rewindPhase (resultControl 0 pairs)))

/-- Real resident classifier: both original operands, every flag, arbitrary
left archive and right suffix are identical on return; both computed nonzero
bits remain in the final phase label. Empty and all-zero inputs are included. -/
theorem residentZero_runsFrom (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom residentZeroMachine (initial archive pairs suffix)
      (trace archive pairs suffix) (final archive pairs suffix) := by
  let r:=resultControl 0 pairs
  let scanLast:=state (haltLabel r) (leftCols pairs.reverse++false::archive) (false::false::suffix)
  let rewindFirst:=padCfg (by decide : 5 ≤ 27)
    (PSTRTMColumnRewind067.state 0 (leftCols pairs.reverse++false::archive) (false::false::suffix))
  let rewindLast:=padCfg (by decide : 5 ≤ 27)
    (PSTRTMColumnRewind067.state 5 (false::archive) (cols pairs++false::false::suffix))
  have hscan : PSTRTMSeq005.RunsFrom (family 0)
      (state (aState 0) (false::archive) (cols pairs++false::false::suffix))
      (ROOTTMGCDZeroTrace007.zeroTrace 0 (false::archive) [] pairs suffix) scanLast := by
    rw [family_zero]
    exact ROOTTMGCDZeroTrace007.zero_runsFrom 0 (false::archive) pairs suffix
  have hrewind : PSTRTMSeq005.RunsFrom (family (rewindPhase r)) rewindFirst
      ((PSTRTMColumnRewind067.fullTrace archive pairs.reverse (false::false::suffix)).map
        (padCfg (by decide : 5 ≤ 27))) rewindLast := by
    rw [family_rewind]
    exact pad_runsFrom (by decide : 5 ≤ 27) PSTRTMColumnRewind067.rewindMachine _ _ _
      (PSTRTMColumnRewind067.rewind_runsFrom archive pairs (false::false::suffix))
  have htransfer : Turing.TM0.step residentZeroMachine (blockCfg (s:=27) (0 : Fin 5) scanLast)=
      some (blockCfg (s:=27) (rewindPhase r) rewindFirst) :=
    block_transfer family ports 0 scanLast (rewindPhase r,0) hscan.2.2.2 (scan_port r)
  have hsegment := segment_append residentZeroMachine _ _ _ _ _ _
    (block_segment family ports 0 _ _ _ hscan)
    (block_segment family ports (rewindPhase r) _ _ _ hrewind) htransfer
  exact segment_runsFrom residentZeroMachine _ _ _ hsegment
    (block_halt family ports (rewindPhase r) rewindLast hrewind.2.2.2 (rewind_port_none r _))

theorem residentZero_length (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (trace archive pairs suffix).length=8*pairs.length+6 := by
  unfold trace
  rw [List.length_append,List.length_map,List.length_map,List.length_map,
    ROOTTMGCDZeroTrace007.zero_length,PSTRTMColumnRewind067.full_length,List.length_reverse]
  omega

theorem residentZero_final_tape (archive : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (final archive pairs suffix).Tape=Turing.Tape.mk₂ (false::archive) (cols pairs++false::false::suffix) := rfl

theorem residentZero_visitedSpace_le (archive : List Bool) (pairs : List (Bool × Bool))
    (suffix : List Bool) (inputLength : Nat) :
    visitedSpace residentZeroMachine inputLength (trace archive pairs suffix) ≤ inputLength+16*pairs.length+13 := by
  have h:=PSTRTMTrace002.visitedSpace_le residentZeroMachine inputLength (trace archive pairs suffix)
  rw [residentZero_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDZeroResident010
