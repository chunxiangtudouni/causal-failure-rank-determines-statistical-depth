module
public import Common.PSTR_TM_ThresholdBadFactor_226
public import Common.PSTR_TM_ThresholdDenPrepare_141

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBackupReturn227
open PaperProofs.Common.Native.RationalControllerComputation

/-! Real retained-B return. TWO moves left reach the old backup EOF;
the existing105 pair rewind then really returns to the first B digit.
Every bit in the factor field and all archive cells are retained. The
new right side contains B ++ TWO FALSE cells ++ factor, so it is NOT
the isolated blank-right B port and is never handed to such a callee. -/

def returnMachine : Machine 6 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdDenPrepare141.twoLeftMachine PSTRTMMulRewind085.rewindMachine

def sourceLeft (archive digits : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks digits.reverse++false::archive

def returnTrace (archive digits suffix : List Bool) : List (MachineState 6) :=
  (PSTRTMThresholdDenPrepare141.twoLeftTrace false false (sourceLeft archive digits) suffix).map
    (PSTRTMSeq005.leftCfg (b := 3)) ++
    (PSTRTMPairRewind105.fullTrace archive digits.reverse (false::false::suffix)).map
      (PSTRTMSeq005.rightCfg (a := 2))

def returnFinal (archive digits suffix : List Bool) : MachineState 6 :=
  PSTRTMSeq005.rightCfg (a := 2) (PSTRTMMulRewind085.state 3 (false::archive)
    (PSTRTMIncrement009.blocks digits++false::false::suffix))

theorem return_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom returnMachine
      ⟨0,Turing.Tape.mk₂ (false::false::sourceLeft archive digits) suffix⟩
      (returnTrace archive digits suffix) (returnFinal archive digits suffix) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMThresholdDenPrepare141.twoLeftMachine
    PSTRTMMulRewind085.rewindMachine
    (PSTRTMThresholdDenPrepare141.state 0 (false::false::sourceLeft archive digits) suffix)
    (PSTRTMThresholdDenPrepare141.state 2 (sourceLeft archive digits) (false::false::suffix))
    (PSTRTMMulRewind085.state 3 (false::archive)
      (PSTRTMIncrement009.blocks digits++false::false::suffix))
    (PSTRTMThresholdDenPrepare141.twoLeftTrace false false (sourceLeft archive digits) suffix)
    (PSTRTMPairRewind105.fullTrace archive digits.reverse (false::false::suffix))
    (PSTRTMThresholdDenPrepare141.twoLeft_runsFrom _ _ _ _)
  exact PSTRTMPairRewind105.rewind_runsFrom archive digits (false::false::suffix)

theorem return_final_tape (archive digits suffix : List Bool) :
    (returnFinal archive digits suffix).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks digits++false::false::suffix) := rfl

theorem return_length (archive digits suffix : List Bool) :
    (returnTrace archive digits suffix).length = 2*digits.length+6 := by
  simp only [returnTrace,List.length_append,List.length_map,
    PSTRTMThresholdDenPrepare141.twoLeftTrace,List.length_cons,List.length_nil,
    PSTRTMPairRewind105.full_length,List.length_reverse]
  omega

theorem return_prefix_space_le (archive digits suffix : List Bool) (input clock : Nat) :
    visitedSpace returnMachine input ((returnTrace archive digits suffix).take clock) ≤
      input+4*digits.length+13 := by
  have hs := PSTRTMTrace002.visitedSpace_le returnMachine input ((returnTrace archive digits suffix).take clock)
  have hl : ((returnTrace archive digits suffix).take clock).length ≤
      (returnTrace archive digits suffix).length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  rw [return_length] at hl
  omega

/-- This is the exact actual boundary of226. It is not a list-only
equality of the printed right side, and does not erase or move a cell. -/
theorem original_factor_entry (risk : Rat) (depth : Nat) :
    (PSTRTMThresholdBadFactor226.factorFinal risk depth).Tape = Turing.Tape.mk₂
      (false::false::sourceLeft (PSTRTMThresholdBBackupEntry188.sourceArchive risk depth)
        (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PSTRTMThresholdBadFactor226.factor risk depth))) := by
  rw [PSTRTMThresholdBadFactor226.factor_final_tape]
  rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBackupReturn227
