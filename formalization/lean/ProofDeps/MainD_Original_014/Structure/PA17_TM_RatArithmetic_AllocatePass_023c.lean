module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMRatArithmeticWidth018

def outDxCoreMachine : Machine 6 := PSTRTMSeq005.seqMachine headerRightMachine outNyMachine
def outDxCoreTrace (left nyTail dyTail suffix : List Bool) : List (MachineState 6) :=
  (headerRightTrace left false false
      (nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))).map
      (PSTRTMSeq005.leftCfg (b:=3)) ++
    (outNyTrace (yHeaderLeft left) (false::nyTail) dyTail suffix).map (PSTRTMSeq005.rightCfg (a:=2))
def outDxCoreFinal (left nyTail dyTail suffix : List Bool) : MachineState 6 :=
  PSTRTMSeq005.rightCfg (a:=2) (outNyFinal (yHeaderLeft left) (false::nyTail) dyTail suffix)

theorem outDxCore_runsFrom (left nyTail dyTail suffix : List Bool) :
    PSTRTMSeq005.RunsFrom outDxCoreMachine
      ⟨0,Turing.Tape.mk₂ left (false::false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))⟩
      (outDxCoreTrace left nyTail dyTail suffix) (outDxCoreFinal left nyTail dyTail suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom headerRightMachine outNyMachine
    (markState 0 left (false::false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))
    (markState 2 (yHeaderLeft left) (nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))
    (outNyFinal (yHeaderLeft left) (false::nyTail) dyTail suffix)
    (headerRightTrace left false false (nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))
    (outNyTrace (yHeaderLeft left) (false::nyTail) dyTail suffix)
    (headerRight_runsFrom left false false (nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))
    (outNy_runsFrom (yHeaderLeft left) (false::nyTail) dyTail suffix)
  simpa only [outDxCoreMachine,outDxCoreTrace,outDxCoreFinal,markState,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

def outDxMachine : Machine 8 := PSTRTMSeq005.seqMachine scanMachine outDxCoreMachine
def outDxTrace (archive later nyTail dyTail suffix : List Bool) : List (MachineState 8) :=
  (scanTrace archive later false
      (false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))).map
      (PSTRTMSeq005.leftCfg (b:=6)) ++
    (outDxCoreTrace (pushField archive later) nyTail dyTail suffix).map (PSTRTMSeq005.rightCfg (a:=1))
def outDxFinal (archive later nyTail dyTail suffix : List Bool) : MachineState 8 :=
  PSTRTMSeq005.rightCfg (a:=1) (outDxCoreFinal (pushField archive later) nyTail dyTail suffix)

theorem outDx_runsFrom (archive later nyTail dyTail suffix : List Bool) :
    PSTRTMSeq005.RunsFrom outDxMachine
      ⟨0,Turing.Tape.mk₂ archive
        (nxStream later (false::false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))⟩
      (outDxTrace archive later nyTail dyTail suffix) (outDxFinal archive later nyTail dyTail suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom scanMachine outDxCoreMachine
    (scanState 0 archive (nxStream later
      (false::false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))))
    (scanState 1 (pushField archive later)
      (false::false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))
    (outDxCoreFinal (pushField archive later) nyTail dyTail suffix)
    (scanTrace archive later false
      (false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))
    (outDxCoreTrace (pushField archive later) nyTail dyTail suffix)
    (scan_runsFrom archive later false
      (false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))
    (outDxCore_runsFrom (pushField archive later) nyTail dyTail suffix)
  simpa only [outDxMachine,outDxTrace,outDxFinal,scanState,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

def outNxMachine : Machine 10 := PSTRTMSeq005.seqMachine scanMachine outDxMachine
def outNxTrace (archive later dxTail nyTail dyTail suffix : List Bool) : List (MachineState 10) :=
  (scanTrace archive later false
      (true::(PSTRTMIncrement009.blocks dxTail++false::false::false::
        nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))).map
      (PSTRTMSeq005.leftCfg (b:=8)) ++
    (outDxTrace (pushField archive later) (false::dxTail) nyTail dyTail suffix).map (PSTRTMSeq005.rightCfg (a:=1))
def outNxFinal (archive later dxTail nyTail dyTail suffix : List Bool) : MachineState 10 :=
  PSTRTMSeq005.rightCfg (a:=1) (outDxFinal (pushField archive later) (false::dxTail) nyTail dyTail suffix)

theorem outNx_runsFrom (archive later dxTail nyTail dyTail suffix : List Bool) :
    PSTRTMSeq005.RunsFrom outNxMachine
      ⟨0,Turing.Tape.mk₂ archive
        (nxStream later (nxStream (false::dxTail) (false::false::
          nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))))⟩
      (outNxTrace archive later dxTail nyTail dyTail suffix) (outNxFinal archive later dxTail nyTail dyTail suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom scanMachine outDxMachine
    (scanState 0 archive (nxStream later (nxStream (false::dxTail)
      (false::false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))))
    (scanState 1 (pushField archive later)
      (false::true::(PSTRTMIncrement009.blocks dxTail++false::false::false::
        nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))))
    (outDxFinal (pushField archive later) (false::dxTail) nyTail dyTail suffix)
    (scanTrace archive later false (true::(PSTRTMIncrement009.blocks dxTail++false::false::false::
      nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))))
    (outDxTrace (pushField archive later) (false::dxTail) nyTail dyTail suffix)
    (scan_runsFrom archive later false (true::(PSTRTMIncrement009.blocks dxTail++false::false::false::
      nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))))
    (outDx_runsFrom (pushField archive later) (false::dxTail) nyTail dyTail suffix)
  simpa only [outNxMachine,outNxTrace,outNxFinal,scanState,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem outDxCoreTrace_length (left nyTail dyTail suffix : List Bool) :
    (outDxCoreTrace left nyTail dyTail suffix).length=2*((false::nyTail).length+(false::dyTail).length)+7 := by
  change (((headerRightTrace left false false
      (nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))).map
      (PSTRTMSeq005.leftCfg (a:=2) (b:=3))) ++
    (outNyTrace (yHeaderLeft left) (false::nyTail) dyTail suffix).map
      (PSTRTMSeq005.rightCfg (a:=2) (b:=3))).length = _
  rw [List.length_append,List.length_map,List.length_map,outNyTrace_length]
  change 3+(2*((false::nyTail).length+(false::dyTail).length)+4) = _
  omega

theorem outDxTrace_length (archive later nyTail dyTail suffix : List Bool) :
    (outDxTrace archive later nyTail dyTail suffix).length=
      2*(later.length+(false::nyTail).length+(false::dyTail).length)+9 := by
  change (((scanTrace archive later false
      (false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))).map
      (PSTRTMSeq005.leftCfg (a:=1) (b:=6))) ++
    (outDxCoreTrace (pushField archive later) nyTail dyTail suffix).map
      (PSTRTMSeq005.rightCfg (a:=1) (b:=6))).length = _
  rw [List.length_append,List.length_map,List.length_map,scanTrace_length,outDxCoreTrace_length]
  omega

theorem outNxTrace_length (archive later dxTail nyTail dyTail suffix : List Bool) :
    (outNxTrace archive later dxTail nyTail dyTail suffix).length=
      2*(later.length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+11 := by
  change (((scanTrace archive later false
      (true::(PSTRTMIncrement009.blocks dxTail++false::false::false::
        nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))).map
      (PSTRTMSeq005.leftCfg (a:=1) (b:=8))) ++
    (outDxTrace (pushField archive later) (false::dxTail) nyTail dyTail suffix).map
      (PSTRTMSeq005.rightCfg (a:=1) (b:=8))).length = _
  rw [List.length_append,List.length_map,List.length_map,scanTrace_length,outDxTrace_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
