module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023d

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticFieldNav012 PA17TMRatArithmeticWidth018

def returnDxCoreMachine : Machine 8 := PSTRTMSeq005.seqMachine headerBackMachine returnDyMachine
def returnDxCoreTrace (archive later right : List Bool) : List (MachineState 8) :=
  (headerBackTrace (pushField (false::archive) later) false false right).map
      (PSTRTMSeq005.leftCfg (b:=5)) ++
    (returnDyTrace archive later (false::false::right)).map (PSTRTMSeq005.rightCfg (a:=2))
def returnDxCoreFinal (archive later right : List Bool) : MachineState 8 :=
  PSTRTMSeq005.rightCfg (a:=2) (returnDyFinal archive later (false::false::right))

theorem returnDxCore_runsFrom (archive later right : List Bool) :
    PSTRTMSeq005.RunsFrom returnDxCoreMachine
      ⟨0,Turing.Tape.mk₂ (yHeaderLeft (pushField (false::archive) later)) right⟩
      (returnDxCoreTrace archive later right) (returnDxCoreFinal archive later right) := by
  have h := PSTRTMSeq005.seq_runsFrom headerBackMachine returnDyMachine
    (headerState 0 (yHeaderLeft (pushField (false::archive) later)) right)
    (headerState 2 (pushField (false::archive) later) (false::false::right))
    (returnDyFinal archive later (false::false::right))
    (headerBackTrace (pushField (false::archive) later) false false right)
    (returnDyTrace archive later (false::false::right))
    (headerBack_runsFrom (pushField (false::archive) later) false false right)
    (returnDy_runsFrom archive later (false::false::right))
  simpa only [returnDxCoreMachine,returnDxCoreTrace,returnDxCoreFinal,headerState,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

def returnDxMachine : Machine 20 := PSTRTMSeq005.seqMachine returnNyMachine returnDxCoreMachine
def returnDxTrace (archive later ny dy suffix : List Bool) : List (MachineState 20) :=
  (returnNyTrace (false::pushField (false::archive) later) ny dy suffix).map
      (PSTRTMSeq005.leftCfg (b:=8)) ++
    (returnDxCoreTrace archive later (nxStream ny (nxStream dy suffix))).map (PSTRTMSeq005.rightCfg (a:=11))
def returnDxFinal (archive later ny dy suffix : List Bool) : MachineState 20 :=
  PSTRTMSeq005.rightCfg (a:=11) (returnDxCoreFinal archive later (nxStream ny (nxStream dy suffix)))

theorem returnDx_runsFrom (archive later ny dy suffix : List Bool) :
    PSTRTMSeq005.RunsFrom returnDxMachine
      ⟨0,Turing.Tape.mk₂
        (pushField (pushField (yHeaderLeft (pushField (false::archive) later)) ny) dy) suffix⟩
      (returnDxTrace archive later ny dy suffix) (returnDxFinal archive later ny dy suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom returnNyMachine returnDxCoreMachine
    (⟨0,Turing.Tape.mk₂ (pushField (pushField (yHeaderLeft (pushField (false::archive) later)) ny) dy) suffix⟩)
    (returnNyFinal (false::pushField (false::archive) later) ny dy suffix)
    (returnDxCoreFinal archive later (nxStream ny (nxStream dy suffix)))
    (returnNyTrace (false::pushField (false::archive) later) ny dy suffix)
    (returnDxCoreTrace archive later (nxStream ny (nxStream dy suffix)))
    (returnNy_runsFrom (false::pushField (false::archive) later) ny dy suffix)
    (returnDxCore_runsFrom archive later (nxStream ny (nxStream dy suffix)))
  simpa only [returnDxMachine,returnDxTrace,returnDxFinal,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

def returnNxMachine : Machine 26 := PSTRTMSeq005.seqMachine returnDxMachine returnDyMachine
def returnNxTrace (archive later dx ny dy suffix : List Bool) : List (MachineState 26) :=
  (returnDxTrace (PSTRTMRawNat010.leftBlocks later.reverse++false::archive) dx ny dy suffix).map
      (PSTRTMSeq005.leftCfg (b:=5)) ++
    (returnDyTrace archive later (nxStream dx (false::false::nxStream ny (nxStream dy suffix)))).map
      (PSTRTMSeq005.rightCfg (a:=20))
def returnNxFinal (archive later dx ny dy suffix : List Bool) : MachineState 26 :=
  PSTRTMSeq005.rightCfg (a:=20)
    (returnDyFinal archive later (nxStream dx (false::false::nxStream ny (nxStream dy suffix))))

theorem returnNx_runsFrom (archive later dx ny dy suffix : List Bool) :
    PSTRTMSeq005.RunsFrom returnNxMachine
      ⟨0,Turing.Tape.mk₂
        (pushField (pushField (yHeaderLeft (pushField (pushField (false::archive) later) dx)) ny) dy) suffix⟩
      (returnNxTrace archive later dx ny dy suffix) (returnNxFinal archive later dx ny dy suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom returnDxMachine returnDyMachine
    (⟨0,Turing.Tape.mk₂
      (pushField (pushField (yHeaderLeft (pushField (pushField (false::archive) later) dx)) ny) dy) suffix⟩)
    (returnDxFinal (PSTRTMRawNat010.leftBlocks later.reverse++false::archive) dx ny dy suffix)
    (returnDyFinal archive later (nxStream dx (false::false::nxStream ny (nxStream dy suffix))))
    (returnDxTrace (PSTRTMRawNat010.leftBlocks later.reverse++false::archive) dx ny dy suffix)
    (returnDyTrace archive later (nxStream dx (false::false::nxStream ny (nxStream dy suffix))))
    (returnDx_runsFrom (PSTRTMRawNat010.leftBlocks later.reverse++false::archive) dx ny dy suffix)
    (returnDy_runsFrom archive later (nxStream dx (false::false::nxStream ny (nxStream dy suffix))))
  simpa only [returnNxMachine,returnNxTrace,returnNxFinal,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem returnDxCoreTrace_length (archive later right : List Bool) :
    (returnDxCoreTrace archive later right).length=2*later.length+8 := by
  change (((headerBackTrace (pushField (false::archive) later) false false right).map
      (PSTRTMSeq005.leftCfg (a:=2) (b:=5))) ++
    (returnDyTrace archive later (false::false::right)).map (PSTRTMSeq005.rightCfg (a:=2) (b:=5))).length = _
  rw [List.length_append,List.length_map,List.length_map,returnDyTrace_length]
  change 3+(2*later.length+5) = _
  omega

theorem returnDxTrace_length (archive later ny dy suffix : List Bool) :
    (returnDxTrace archive later ny dy suffix).length=2*(later.length+ny.length+dy.length)+18 := by
  change (((returnNyTrace (false::pushField (false::archive) later) ny dy suffix).map
      (PSTRTMSeq005.leftCfg (a:=11) (b:=8))) ++
    (returnDxCoreTrace archive later (nxStream ny (nxStream dy suffix))).map
      (PSTRTMSeq005.rightCfg (a:=11) (b:=8))).length = _
  rw [List.length_append,List.length_map,List.length_map,returnNyTrace_length,returnDxCoreTrace_length]
  omega

theorem returnNxTrace_length (archive later dx ny dy suffix : List Bool) :
    (returnNxTrace archive later dx ny dy suffix).length=2*(later.length+dx.length+ny.length+dy.length)+23 := by
  change (((returnDxTrace (PSTRTMRawNat010.leftBlocks later.reverse++false::archive) dx ny dy suffix).map
      (PSTRTMSeq005.leftCfg (a:=20) (b:=5))) ++
    (returnDyTrace archive later (nxStream dx (false::false::nxStream ny (nxStream dy suffix)))).map
      (PSTRTMSeq005.rightCfg (a:=20) (b:=5))).length = _
  rw [List.length_append,List.length_map,List.length_map,returnDxTrace_length,returnDyTrace_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
