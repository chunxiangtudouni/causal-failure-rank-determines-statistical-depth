module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023c

/-! Reverse following fields, then stop immediately after the actual
temporary FALSE flag. The marker itself is retained for the paid restore.
The whole later suffix, including the new gap, is preserved verbatim. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticWidth018

def returnDyMachine : Machine 5 := fieldBackMachine
def returnDyTrace (archive later suffix : List Bool) : List (MachineState 5) := fieldBackTrace archive later suffix
def returnDyFinal (archive later suffix : List Bool) : MachineState 5 := fieldBackFinal archive later suffix

theorem returnDy_runsFrom (archive later suffix : List Bool) :
    PSTRTMSeq005.RunsFrom returnDyMachine
      ⟨0,Turing.Tape.mk₂ (pushField (false::archive) later) suffix⟩
      (returnDyTrace archive later suffix) (returnDyFinal archive later suffix) := fieldBack_runsFrom archive later suffix

theorem returnDyTrace_length (archive later suffix : List Bool) :
    (returnDyTrace archive later suffix).length=2*later.length+5 := fieldBackTrace_length archive later suffix

def returnNyMachine : Machine 11 := PSTRTMSeq005.seqMachine fieldBackMachine returnDyMachine
def returnNyTrace (archive later dy suffix : List Bool) : List (MachineState 11) :=
  (fieldBackTrace (PSTRTMRawNat010.leftBlocks later.reverse++false::archive) dy suffix).map
      (PSTRTMSeq005.leftCfg (b:=5)) ++
    (returnDyTrace archive later (nxStream dy suffix)).map (PSTRTMSeq005.rightCfg (a:=5))
def returnNyFinal (archive later dy suffix : List Bool) : MachineState 11 :=
  PSTRTMSeq005.rightCfg (a:=5) (returnDyFinal archive later (nxStream dy suffix))

theorem returnNy_runsFrom (archive later dy suffix : List Bool) :
    PSTRTMSeq005.RunsFrom returnNyMachine
      ⟨0,Turing.Tape.mk₂ (pushField (pushField (false::archive) later) dy) suffix⟩
      (returnNyTrace archive later dy suffix) (returnNyFinal archive later dy suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom fieldBackMachine returnDyMachine
    (⟨0,Turing.Tape.mk₂ (pushField (pushField (false::archive) later) dy) suffix⟩)
    (fieldBackFinal (PSTRTMRawNat010.leftBlocks later.reverse++false::archive) dy suffix)
    (returnDyFinal archive later (nxStream dy suffix))
    (fieldBackTrace (PSTRTMRawNat010.leftBlocks later.reverse++false::archive) dy suffix)
    (returnDyTrace archive later (nxStream dy suffix))
    (fieldBack_runsFrom (PSTRTMRawNat010.leftBlocks later.reverse++false::archive) dy suffix)
    (returnDy_runsFrom archive later (nxStream dy suffix))
  simpa only [returnNyMachine,returnNyTrace,returnNyFinal,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem returnNy_final_tape (archive later dy suffix : List Bool) :
    (returnNyFinal archive later dy suffix).Tape=
      Turing.Tape.mk₂ (false::archive) (nxStream later (nxStream dy suffix)) := rfl

theorem returnNyTrace_length (archive later dy suffix : List Bool) :
    (returnNyTrace archive later dy suffix).length=2*(later.length+dy.length)+10 := by
  change (((fieldBackTrace (PSTRTMRawNat010.leftBlocks later.reverse++false::archive) dy suffix).map
      (PSTRTMSeq005.leftCfg (a:=5) (b:=5))) ++
    (returnDyTrace archive later (nxStream dy suffix)).map
      (PSTRTMSeq005.rightCfg (a:=5) (b:=5))).length = _
  rw [List.length_append,List.length_map,List.length_map,fieldBackTrace_length,returnDyTrace_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
