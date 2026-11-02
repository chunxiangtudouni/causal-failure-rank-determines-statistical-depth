module
public import Structure.PA17_TM_RatArithmetic_Width_018c

/-! Four fixed reverse routes from an actual field first-data cell to
the original input header. Every field rewind and the y-sign crossing
is physical. The current field's entire right stream is arbitrary. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticFieldNav012

def nxContext (sx : Bool) (counter : List Bool) : List Bool := [sx,true,false,false,true,true]++counter
def dxContext (sx : Bool) (counter nx : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks nx.reverse++false::nxContext sx counter
def nyContext (sx : Bool) (counter nx dx : List Bool) : List Bool :=
  false::false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx)
def dyContext (sx : Bool) (counter nx dx ny : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks ny.reverse++false::nyContext sx counter nx dx

def nxStream (nx right : List Bool) : List Bool := PSTRTMIncrement009.blocks nx++false::right
def nyStream (nx dx right : List Bool) : List Bool := nxStream nx (nxStream dx (false::false::right))
def dyStream (nx dx ny right : List Bool) : List Bool := nyStream nx dx (nxStream ny right)

def backNxMachine : Machine 7 := sevenMachine .left
def backNxTrace (sx : Bool) (counter right : List Bool) : List (MachineState 7) := leftSevenTrace sx counter right
def backNxFinal (sx : Bool) (counter right : List Bool) : MachineState 7 := sevenState 7 counter (prefixRight sx right)

theorem backNx_runsFrom (sx : Bool) (counter right : List Bool) :
    PSTRTMSeq005.RunsFrom backNxMachine ⟨0,Turing.Tape.mk₂ (false::nxContext sx counter) right⟩
      (backNxTrace sx counter right) (backNxFinal sx counter right) := leftSeven_runsFrom sx counter right

def backDxMachine : Machine 13 := PSTRTMSeq005.seqMachine fieldBackMachine backNxMachine
def backDxTrace (sx : Bool) (counter nx right : List Bool) : List (MachineState 13) :=
  (fieldBackTrace (nxContext sx counter) nx right).map (PSTRTMSeq005.leftCfg (b:=7)) ++
    (backNxTrace sx counter (nxStream nx right)).map (PSTRTMSeq005.rightCfg (a:=5))
def backDxFinal (sx : Bool) (counter nx right : List Bool) : MachineState 13 :=
  PSTRTMSeq005.rightCfg (a:=5) (backNxFinal sx counter (nxStream nx right))

theorem backDx_runsFrom (sx : Bool) (counter nx right : List Bool) :
    PSTRTMSeq005.RunsFrom backDxMachine ⟨0,Turing.Tape.mk₂ (false::dxContext sx counter nx) right⟩
      (backDxTrace sx counter nx right) (backDxFinal sx counter nx right) := by
  have h := PSTRTMSeq005.seq_runsFrom fieldBackMachine backNxMachine
    (⟨0,Turing.Tape.mk₂ (false::dxContext sx counter nx) right⟩)
    (fieldBackFinal (nxContext sx counter) nx right)
    (backNxFinal sx counter (nxStream nx right))
    (fieldBackTrace (nxContext sx counter) nx right) (backNxTrace sx counter (nxStream nx right))
    (fieldBack_runsFrom (nxContext sx counter) nx right)
    (backNx_runsFrom sx counter (nxStream nx right))
  simpa only [backDxMachine,backDxTrace,backDxFinal,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

def backNyCoreMachine : Machine 19 := PSTRTMSeq005.seqMachine fieldBackMachine backDxMachine
def backNyCoreTrace (sx : Bool) (counter nx dx right : List Bool) : List (MachineState 19) :=
  (fieldBackTrace (dxContext sx counter nx) dx (false::false::right)).map (PSTRTMSeq005.leftCfg (b:=13)) ++
    (backDxTrace sx counter nx (nxStream dx (false::false::right))).map (PSTRTMSeq005.rightCfg (a:=5))
def backNyCoreFinal (sx : Bool) (counter nx dx right : List Bool) : MachineState 19 :=
  PSTRTMSeq005.rightCfg (a:=5) (backDxFinal sx counter nx (nxStream dx (false::false::right)))

theorem backNyCore_runsFrom (sx : Bool) (counter nx dx right : List Bool) :
    PSTRTMSeq005.RunsFrom backNyCoreMachine
      ⟨0,Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
        (false::false::right)⟩
      (backNyCoreTrace sx counter nx dx right) (backNyCoreFinal sx counter nx dx right) := by
  have h := PSTRTMSeq005.seq_runsFrom fieldBackMachine backDxMachine
    (⟨0,Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      (false::false::right)⟩)
    (fieldBackFinal (dxContext sx counter nx) dx (false::false::right))
    (backDxFinal sx counter nx (nxStream dx (false::false::right)))
    (fieldBackTrace (dxContext sx counter nx) dx (false::false::right))
    (backDxTrace sx counter nx (nxStream dx (false::false::right)))
    (fieldBack_runsFrom (dxContext sx counter nx) dx (false::false::right))
    (backDx_runsFrom sx counter nx (nxStream dx (false::false::right)))
  simpa only [backNyCoreMachine,backNyCoreTrace,backNyCoreFinal,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

def backNyMachine : Machine 22 := PSTRTMSeq005.seqMachine headerBackMachine backNyCoreMachine
def backNyTrace (sx : Bool) (counter nx dx right : List Bool) : List (MachineState 22) :=
  (headerBackTrace (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      false false right).map (PSTRTMSeq005.leftCfg (b:=19)) ++
    (backNyCoreTrace sx counter nx dx right).map (PSTRTMSeq005.rightCfg (a:=2))
def backNyFinal (sx : Bool) (counter nx dx right : List Bool) : MachineState 22 :=
  PSTRTMSeq005.rightCfg (a:=2) (backNyCoreFinal sx counter nx dx right)

theorem backNy_runsFrom (sx : Bool) (counter nx dx right : List Bool) :
    PSTRTMSeq005.RunsFrom backNyMachine
      ⟨0,Turing.Tape.mk₂ (false::nyContext sx counter nx dx) right⟩
      (backNyTrace sx counter nx dx right) (backNyFinal sx counter nx dx right) := by
  have h := PSTRTMSeq005.seq_runsFrom headerBackMachine backNyCoreMachine
    (headerState 0 (false::nyContext sx counter nx dx) right)
    (headerState 2 (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      (false::false::right))
    (backNyCoreFinal sx counter nx dx right)
    (headerBackTrace (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      false false right)
    (backNyCoreTrace sx counter nx dx right)
    (headerBack_runsFrom (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      false false right)
    (backNyCore_runsFrom sx counter nx dx right)
  simpa only [backNyMachine,backNyTrace,backNyFinal,headerState,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

def backDyMachine : Machine 28 := PSTRTMSeq005.seqMachine fieldBackMachine backNyMachine
def backDyTrace (sx : Bool) (counter nx dx ny right : List Bool) : List (MachineState 28) :=
  (fieldBackTrace (nyContext sx counter nx dx) ny right).map (PSTRTMSeq005.leftCfg (b:=22)) ++
    (backNyTrace sx counter nx dx (nxStream ny right)).map (PSTRTMSeq005.rightCfg (a:=5))
def backDyFinal (sx : Bool) (counter nx dx ny right : List Bool) : MachineState 28 :=
  PSTRTMSeq005.rightCfg (a:=5) (backNyFinal sx counter nx dx (nxStream ny right))

theorem backDy_runsFrom (sx : Bool) (counter nx dx ny right : List Bool) :
    PSTRTMSeq005.RunsFrom backDyMachine
      ⟨0,Turing.Tape.mk₂ (false::dyContext sx counter nx dx ny) right⟩
      (backDyTrace sx counter nx dx ny right) (backDyFinal sx counter nx dx ny right) := by
  have h := PSTRTMSeq005.seq_runsFrom fieldBackMachine backNyMachine
    (⟨0,Turing.Tape.mk₂ (false::dyContext sx counter nx dx ny) right⟩)
    (fieldBackFinal (nyContext sx counter nx dx) ny right)
    (backNyFinal sx counter nx dx (nxStream ny right))
    (fieldBackTrace (nyContext sx counter nx dx) ny right)
    (backNyTrace sx counter nx dx (nxStream ny right))
    (fieldBack_runsFrom (nyContext sx counter nx dx) ny right)
    (backNy_runsFrom sx counter nx dx (nxStream ny right))
  simpa only [backDyMachine,backDyTrace,backDyFinal,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem backDx_final_tape (sx : Bool) (counter nx right : List Bool) :
    (backDxFinal sx counter nx right).Tape=Turing.Tape.mk₂ counter (prefixRight sx (nxStream nx right)) := rfl
theorem backNy_final_tape (sx : Bool) (counter nx dx right : List Bool) :
    (backNyFinal sx counter nx dx right).Tape=Turing.Tape.mk₂ counter (prefixRight sx (nyStream nx dx right)) := rfl
theorem backDy_final_tape (sx : Bool) (counter nx dx ny right : List Bool) :
    (backDyFinal sx counter nx dx ny right).Tape=Turing.Tape.mk₂ counter (prefixRight sx (dyStream nx dx ny right)) := rfl

theorem backNxTrace_length (sx : Bool) (counter right : List Bool) : (backNxTrace sx counter right).length=8 := rfl
theorem backDxTrace_length (sx : Bool) (counter nx right : List Bool) :
    (backDxTrace sx counter nx right).length=2*nx.length+13 := by
  change (((fieldBackTrace (nxContext sx counter) nx right).map (PSTRTMSeq005.leftCfg (a:=5) (b:=7))) ++
    (backNxTrace sx counter (nxStream nx right)).map (PSTRTMSeq005.rightCfg (a:=5) (b:=7))).length = _
  rw [List.length_append,List.length_map,List.length_map,fieldBackTrace_length,backNxTrace_length]
theorem backNyCoreTrace_length (sx : Bool) (counter nx dx right : List Bool) :
    (backNyCoreTrace sx counter nx dx right).length=2*(nx.length+dx.length)+18 := by
  change (((fieldBackTrace (dxContext sx counter nx) dx (false::false::right)).map
      (PSTRTMSeq005.leftCfg (a:=5) (b:=13))) ++
    (backDxTrace sx counter nx (nxStream dx (false::false::right))).map
      (PSTRTMSeq005.rightCfg (a:=5) (b:=13))).length = _
  rw [List.length_append,List.length_map,List.length_map,fieldBackTrace_length,backDxTrace_length]
  omega
theorem backNyTrace_length (sx : Bool) (counter nx dx right : List Bool) :
    (backNyTrace sx counter nx dx right).length=2*(nx.length+dx.length)+21 := by
  change (((headerBackTrace (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      false false right).map (PSTRTMSeq005.leftCfg (a:=2) (b:=19))) ++
    (backNyCoreTrace sx counter nx dx right).map (PSTRTMSeq005.rightCfg (a:=2) (b:=19))).length = _
  rw [List.length_append,List.length_map,List.length_map,backNyCoreTrace_length]
  change 3+(2*(nx.length+dx.length)+18) = _
  omega
theorem backDyTrace_length (sx : Bool) (counter nx dx ny right : List Bool) :
    (backDyTrace sx counter nx dx ny right).length=2*(nx.length+dx.length+ny.length)+26 := by
  change (((fieldBackTrace (nyContext sx counter nx dx) ny right).map (PSTRTMSeq005.leftCfg (a:=5) (b:=22))) ++
    (backNyTrace sx counter nx dx (nxStream ny right)).map (PSTRTMSeq005.rightCfg (a:=5) (b:=22))).length = _
  rw [List.length_append,List.length_map,List.length_map,fieldBackTrace_length,backNyTrace_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
