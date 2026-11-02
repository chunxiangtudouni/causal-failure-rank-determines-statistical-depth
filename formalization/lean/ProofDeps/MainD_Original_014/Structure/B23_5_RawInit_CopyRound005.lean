module
public import Common.PSTR_WordBool_RawInit_MarkAppend016
public import Common.PSTR_WordBool_RawInit_Restore015
public import Structure.PA17_RawInit_RowReturn_Contract003

/-! Physical one-bit reverse-export round. The real MarkAppend endpoint
matches RowReturn with gap+1 and left=selectedLeft. Its TRUE return sentinel
is already the entry cell for the frozen Restore scanner (q0 LEFT, q1
pair-reverse payload LEFT, q2 FALSE flag LEFT / TRUE marker WRITE false,
q3 LEFT to the next source cell). No extra tape or host-selected bit port.
-/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.CopyRound
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

def prefixMachine : Machine 414 := seqMachine MarkAppend.machine PA17RawInitRowReturn.machine
def machine : Machine 419 := seqMachine prefixMachine Restore.machine
def outputSuffix (bits : List Bool) (bit : Bool) (gap : Nat) : List Bool :=
  true :: (List.replicate (gap+1) false ++ RowEnd.rows (bits++[bit]))
def initial (left higher : List Bool) (bit : Bool) (gap : Nat) (bits : List Bool) : MachineState 419 :=
  leftCfg (b:=4) (leftCfg (b:=34) (MarkAppend.initial left higher bit gap bits))
def final (left higher : List Bool) (bit : Bool) (gap : Nat) (bits : List Bool) : MachineState 419 :=
  rightCfg (a:=414) (Restore.final left higher bit (outputSuffix bits bit gap))

theorem append_return_tape (left higher : List Bool) (bit : Bool) (gap : Nat) (bits : List Bool) :
    (MarkAppend.final left higher bit gap bits).Tape =
      PA17RawInitRowReturn.initialTape (bits++[bit]) (gap+1)
        (MarkSeek.selectedLeft left higher bit) [] := by
  simp only [MarkAppend.final,MarkAppend.sourceLeft,PA17RawInitRowReturn.initialTape,
    List.append_assoc]
  rw [PA17RawInitRowReturn.zeros_snoc gap (true::MarkSeek.selectedLeft left higher bit)]
  rfl

theorem return_restore_tape (left higher : List Bool) (bit : Bool) (gap : Nat) (bits : List Bool) :
    PA17RawInitRowReturn.finalTape (bits++[bit]) (gap+1)
      (MarkSeek.selectedLeft left higher bit) [] =
      (Restore.initial left higher bit (outputSuffix bits bit gap)).Tape := by
  simp only [PA17RawInitRowReturn.finalTape,PA17RawInitRowReturn.rows,
    Restore.initial,Restore.state,MarkSeek.selectedLeft,outputSuffix,RowEnd.rows,List.append_nil]

theorem actual (left higher : List Bool) (bit : Bool) (gap : Nat) (bits : List Bool)
    (inputLength : Nat) :
    ∃ path, RunsFrom machine (initial left higher bit gap bits) path
        (final left higher bit gap bits) ∧
      path.length=4*higher.length+2*gap+67*(bits.length+1)+118 ∧
      ∀ clock, visitedSpace machine inputLength (path.take clock)≤
        inputLength+2*(4*higher.length+2*gap+67*(bits.length+1)+118)+1 := by
  obtain ⟨append,appendRun,appendTime,_appendSpace⟩ :=
    MarkAppend.actual left higher bit gap bits inputLength
  obtain ⟨returnPath,returnRun,returnTime⟩ :=
    PA17RawInitRowReturn.rows_run (bits++[bit]) (gap+1)
      (MarkSeek.selectedLeft left higher bit) []
  have returnRun' : RunsFrom PA17RawInitRowReturn.machine
      ⟨0,(MarkAppend.final left higher bit gap bits).Tape⟩ returnPath
      (PA17RawInitRowReturn.state 34 (PA17RawInitRowReturn.finalTape
        (bits++[bit]) (gap+1) (MarkSeek.selectedLeft left higher bit) [])) := by
    rw [append_return_tape]
    exact returnRun
  let frontTrace := append.map (leftCfg (b:=34))++returnPath.map (rightCfg (a:=379))
  let prefixFinal := rightCfg (a:=379) (PA17RawInitRowReturn.state 34
    (PA17RawInitRowReturn.finalTape (bits++[bit]) (gap+1)
      (MarkSeek.selectedLeft left higher bit) []))
  have prefixRun : RunsFrom prefixMachine
      (leftCfg (b:=34) (MarkAppend.initial left higher bit gap bits)) frontTrace prefixFinal :=
    seq_runsFrom MarkAppend.machine PA17RawInitRowReturn.machine _ _ _
      append returnPath appendRun returnRun'
  obtain ⟨restorePath,restoreRun,restoreTime,_restoreSpace⟩ :=
    Restore.actual left higher bit (outputSuffix bits bit gap) inputLength
  have restoreRun' : RunsFrom Restore.machine ⟨0,prefixFinal.Tape⟩ restorePath
      (Restore.final left higher bit (outputSuffix bits bit gap)) := by
    change RunsFrom _ ⟨0,PA17RawInitRowReturn.finalTape (bits++[bit]) (gap+1)
      (MarkSeek.selectedLeft left higher bit) []⟩ _ _
    rw [return_restore_tape]
    exact restoreRun
  let path := frontTrace.map (leftCfg (b:=4))++restorePath.map (rightCfg (a:=414))
  have run := seq_runsFrom prefixMachine Restore.machine _ _ _ frontTrace restorePath
    prefixRun restoreRun'
  have time : path.length=4*higher.length+2*gap+67*(bits.length+1)+118 := by
    simp only [path,frontTrace,List.length_append,List.length_map,appendTime,
      returnTime,restoreTime,List.length_singleton]
    omega
  refine ⟨path,run,time,?_⟩
  intro clock
  have cells := PSTRTMTrace002.visitedSpace_le machine inputLength (path.take clock)
  have take := List.length_take_le' clock path
  rw [time] at take
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.CopyRound
