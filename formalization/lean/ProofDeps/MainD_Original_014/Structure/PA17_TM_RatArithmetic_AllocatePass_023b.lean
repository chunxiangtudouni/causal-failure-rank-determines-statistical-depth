module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023a

/-! Outbound routes from after the current temporary flag. Each scanner
really reaches its FALSE boundary; the original footer is never skipped.
The later source field's first DATA has already been clamped by014. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMRatArithmeticWidth018

def outDyMachine : Machine 1 := scanMachine
def outDyTrace (archive digits suffix : List Bool) : List (MachineState 1) := scanTrace archive digits false suffix
def outDyFinal (archive digits suffix : List Bool) : MachineState 1 :=
  scanState 1 (pushField archive digits) (false::suffix)

theorem outDy_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom outDyMachine
      ⟨0,Turing.Tape.mk₂ archive (nxStream digits (false::suffix))⟩
      (outDyTrace archive digits suffix) (outDyFinal archive digits suffix) := scan_runsFrom archive digits false suffix

theorem outDyTrace_length (archive digits suffix : List Bool) :
    (outDyTrace archive digits suffix).length=2*digits.length+2 := scanTrace_length archive digits false suffix

def outNyMachine : Machine 3 := PSTRTMSeq005.seqMachine scanMachine outDyMachine
def outNyTrace (archive later dyTail suffix : List Bool) : List (MachineState 3) :=
  (scanTrace archive later false (true::(PSTRTMIncrement009.blocks dyTail++false::false::suffix))).map
      (PSTRTMSeq005.leftCfg (b:=1)) ++
    (outDyTrace (pushField archive later) (false::dyTail) suffix).map (PSTRTMSeq005.rightCfg (a:=1))
def outNyFinal (archive later dyTail suffix : List Bool) : MachineState 3 :=
  PSTRTMSeq005.rightCfg (a:=1) (outDyFinal (pushField archive later) (false::dyTail) suffix)

theorem outNy_runsFrom (archive later dyTail suffix : List Bool) :
    PSTRTMSeq005.RunsFrom outNyMachine
      ⟨0,Turing.Tape.mk₂ archive (nxStream later (nxStream (false::dyTail) (false::suffix)))⟩
      (outNyTrace archive later dyTail suffix) (outNyFinal archive later dyTail suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom scanMachine outDyMachine
    (scanState 0 archive (nxStream later (nxStream (false::dyTail) (false::suffix))))
    (scanState 1 (pushField archive later)
      (false::true::(PSTRTMIncrement009.blocks dyTail++false::false::suffix)))
    (outDyFinal (pushField archive later) (false::dyTail) suffix)
    (scanTrace archive later false (true::(PSTRTMIncrement009.blocks dyTail++false::false::suffix)))
    (outDyTrace (pushField archive later) (false::dyTail) suffix)
    (scan_runsFrom archive later false (true::(PSTRTMIncrement009.blocks dyTail++false::false::suffix)))
    (outDy_runsFrom (pushField archive later) (false::dyTail) suffix)
  simpa only [outNyMachine,outNyTrace,outNyFinal,scanState,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem outNy_final_tape (archive later dyTail suffix : List Bool) :
    (outNyFinal archive later dyTail suffix).Tape=
      Turing.Tape.mk₂ (pushField (pushField archive later) (false::dyTail)) (false::suffix) := rfl

theorem outNyTrace_length (archive later dyTail suffix : List Bool) :
    (outNyTrace archive later dyTail suffix).length=2*(later.length+(false::dyTail).length)+4 := by
  change (((scanTrace archive later false (true::(PSTRTMIncrement009.blocks dyTail++false::false::suffix))).map
      (PSTRTMSeq005.leftCfg (a:=1) (b:=1))) ++
    (outDyTrace (pushField archive later) (false::dyTail) suffix).map
      (PSTRTMSeq005.rightCfg (a:=1) (b:=1))).length = _
  rw [List.length_append,List.length_map,List.length_map,scanTrace_length,outDyTrace_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
