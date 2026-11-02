module
public import Structure.PA17_TM_RatArithmetic_Width_018d

/-! Fixed forward routes. Only already established FALSE boundary cells
are used as stops. The y sign and guard are crossed by two paid RIGHTs.
The target stream, including its temporary marker, is retained verbatim. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018

def forwardNxMachine : Machine 7 := sevenMachine .right
def forwardNxTrace (sx : Bool) (counter right : List Bool) : List (MachineState 7) := rightSevenTrace sx counter right
def forwardNxFinal (sx : Bool) (counter right : List Bool) : MachineState 7 := sevenState 7 (prefixLeft sx counter) right

theorem forwardNx_runsFrom (sx : Bool) (counter right : List Bool) :
    PSTRTMSeq005.RunsFrom forwardNxMachine ⟨0,Turing.Tape.mk₂ counter (prefixRight sx right)⟩
      (forwardNxTrace sx counter right) (forwardNxFinal sx counter right) := rightSeven_runsFrom sx counter right

def forwardDxMachine : Machine 9 := PSTRTMSeq005.seqMachine forwardNxMachine scanMachine
def forwardDxTrace (sx : Bool) (counter nx tail : List Bool) : List (MachineState 9) :=
  (forwardNxTrace sx counter (nxStream nx (false::tail))).map (PSTRTMSeq005.leftCfg (b:=1)) ++
    (scanTrace (prefixLeft sx counter) nx false tail).map (PSTRTMSeq005.rightCfg (a:=7))
def forwardDxFinal (sx : Bool) (counter nx tail : List Bool) : MachineState 9 :=
  PSTRTMSeq005.rightCfg (a:=7) (scanState 1 (false::dxContext sx counter nx) (false::tail))

theorem forwardDx_runsFrom (sx : Bool) (counter nx tail : List Bool) :
    PSTRTMSeq005.RunsFrom forwardDxMachine
      ⟨0,Turing.Tape.mk₂ counter (prefixRight sx (nxStream nx (false::tail)))⟩
      (forwardDxTrace sx counter nx tail) (forwardDxFinal sx counter nx tail) := by
  have h := PSTRTMSeq005.seq_runsFrom forwardNxMachine scanMachine
    (⟨0,Turing.Tape.mk₂ counter (prefixRight sx (nxStream nx (false::tail)))⟩)
    (forwardNxFinal sx counter (nxStream nx (false::tail)))
    (scanState 1 (false::dxContext sx counter nx) (false::tail))
    (forwardNxTrace sx counter (nxStream nx (false::tail)))
    (scanTrace (prefixLeft sx counter) nx false tail)
    (forwardNx_runsFrom sx counter (nxStream nx (false::tail)))
    (scan_runsFrom (prefixLeft sx counter) nx false tail)
  simpa only [forwardDxMachine,forwardDxTrace,forwardDxFinal,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

def forwardNyCoreMachine : Machine 4 := PSTRTMSeq005.seqMachine scanMachine headerRightMachine
def forwardNyCoreTrace (sx : Bool) (counter nx dx right : List Bool) : List (MachineState 4) :=
  (scanTrace (false::dxContext sx counter nx) dx false (false::right)).map
      (PSTRTMSeq005.leftCfg (b:=2)) ++
    (headerRightTrace (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      false false right).map (PSTRTMSeq005.rightCfg (a:=1))
def forwardNyCoreFinal (sx : Bool) (counter nx dx right : List Bool) : MachineState 4 :=
  PSTRTMSeq005.rightCfg (a:=1) (markState 2 (false::nyContext sx counter nx dx) right)

theorem forwardNyCore_runsFrom (sx : Bool) (counter nx dx right : List Bool) :
    PSTRTMSeq005.RunsFrom forwardNyCoreMachine
      ⟨0,Turing.Tape.mk₂ (false::dxContext sx counter nx) (nxStream dx (false::false::right))⟩
      (forwardNyCoreTrace sx counter nx dx right) (forwardNyCoreFinal sx counter nx dx right) := by
  have h := PSTRTMSeq005.seq_runsFrom scanMachine headerRightMachine
    (scanState 0 (false::dxContext sx counter nx) (nxStream dx (false::false::right)))
    (scanState 1 (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      (false::false::right))
    (markState 2 (false::nyContext sx counter nx dx) right)
    (scanTrace (false::dxContext sx counter nx) dx false (false::right))
    (headerRightTrace (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      false false right)
    (scan_runsFrom (false::dxContext sx counter nx) dx false (false::right))
    (headerRight_runsFrom (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      false false right)
  simpa only [forwardNyCoreMachine,forwardNyCoreTrace,forwardNyCoreFinal,scanState,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

def forwardNyMachine : Machine 14 := PSTRTMSeq005.seqMachine forwardDxMachine forwardNyCoreMachine
def forwardNyTrace (sx : Bool) (counter nx dxTail right : List Bool) : List (MachineState 14) :=
  (forwardDxTrace sx counter nx (true::(PSTRTMIncrement009.blocks dxTail++false::false::false::right))).map
      (PSTRTMSeq005.leftCfg (b:=4)) ++
    (forwardNyCoreTrace sx counter nx (false::dxTail) right).map (PSTRTMSeq005.rightCfg (a:=9))
def forwardNyFinal (sx : Bool) (counter nx dxTail right : List Bool) : MachineState 14 :=
  PSTRTMSeq005.rightCfg (a:=9) (forwardNyCoreFinal sx counter nx (false::dxTail) right)

theorem forwardNy_runsFrom (sx : Bool) (counter nx dxTail right : List Bool) :
    PSTRTMSeq005.RunsFrom forwardNyMachine
      ⟨0,Turing.Tape.mk₂ counter (prefixRight sx (nyStream nx (false::dxTail) right))⟩
      (forwardNyTrace sx counter nx dxTail right) (forwardNyFinal sx counter nx dxTail right) := by
  have h := PSTRTMSeq005.seq_runsFrom forwardDxMachine forwardNyCoreMachine
    (⟨0,Turing.Tape.mk₂ counter (prefixRight sx (nyStream nx (false::dxTail) right))⟩)
    (forwardDxFinal sx counter nx (true::(PSTRTMIncrement009.blocks dxTail++false::false::false::right)))
    (forwardNyCoreFinal sx counter nx (false::dxTail) right)
    (forwardDxTrace sx counter nx (true::(PSTRTMIncrement009.blocks dxTail++false::false::false::right)))
    (forwardNyCoreTrace sx counter nx (false::dxTail) right)
    (forwardDx_runsFrom sx counter nx (true::(PSTRTMIncrement009.blocks dxTail++false::false::false::right)))
    (forwardNyCore_runsFrom sx counter nx (false::dxTail) right)
  simpa only [forwardNyMachine,forwardNyTrace,forwardNyFinal,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

def forwardDyMachine : Machine 16 := PSTRTMSeq005.seqMachine forwardNyMachine scanMachine
def forwardDyTrace (sx : Bool) (counter nx dxTail ny tail : List Bool) : List (MachineState 16) :=
  (forwardNyTrace sx counter nx dxTail (nxStream ny (false::tail))).map (PSTRTMSeq005.leftCfg (b:=1)) ++
    (scanTrace (false::nyContext sx counter nx (false::dxTail)) ny false tail).map
      (PSTRTMSeq005.rightCfg (a:=14))
def forwardDyFinal (sx : Bool) (counter nx dxTail ny tail : List Bool) : MachineState 16 :=
  PSTRTMSeq005.rightCfg (a:=14)
    (scanState 1 (false::dyContext sx counter nx (false::dxTail) ny) (false::tail))

theorem forwardDy_runsFrom (sx : Bool) (counter nx dxTail ny tail : List Bool) :
    PSTRTMSeq005.RunsFrom forwardDyMachine
      ⟨0,Turing.Tape.mk₂ counter (prefixRight sx (dyStream nx (false::dxTail) ny (false::tail)))⟩
      (forwardDyTrace sx counter nx dxTail ny tail) (forwardDyFinal sx counter nx dxTail ny tail) := by
  have h := PSTRTMSeq005.seq_runsFrom forwardNyMachine scanMachine
    (⟨0,Turing.Tape.mk₂ counter (prefixRight sx (dyStream nx (false::dxTail) ny (false::tail)))⟩)
    (forwardNyFinal sx counter nx dxTail (nxStream ny (false::tail)))
    (scanState 1 (false::dyContext sx counter nx (false::dxTail) ny) (false::tail))
    (forwardNyTrace sx counter nx dxTail (nxStream ny (false::tail)))
    (scanTrace (false::nyContext sx counter nx (false::dxTail)) ny false tail)
    (forwardNy_runsFrom sx counter nx dxTail (nxStream ny (false::tail)))
    (scan_runsFrom (false::nyContext sx counter nx (false::dxTail)) ny false tail)
  simpa only [forwardDyMachine,forwardDyTrace,forwardDyFinal,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem forwardNxTrace_length (sx : Bool) (counter right : List Bool) : (forwardNxTrace sx counter right).length=8 := rfl
theorem forwardDxTrace_length (sx : Bool) (counter nx tail : List Bool) :
    (forwardDxTrace sx counter nx tail).length=2*nx.length+10 := by
  change (((forwardNxTrace sx counter (nxStream nx (false::tail))).map (PSTRTMSeq005.leftCfg (a:=7) (b:=1))) ++
    (scanTrace (prefixLeft sx counter) nx false tail).map (PSTRTMSeq005.rightCfg (a:=7) (b:=1))).length = _
  rw [List.length_append,List.length_map,List.length_map,forwardNxTrace_length,scanTrace_length]
  omega
theorem forwardNyCoreTrace_length (sx : Bool) (counter nx dx right : List Bool) :
    (forwardNyCoreTrace sx counter nx dx right).length=2*dx.length+5 := by
  change (((scanTrace (false::dxContext sx counter nx) dx false (false::right)).map
      (PSTRTMSeq005.leftCfg (a:=1) (b:=2))) ++
    (headerRightTrace (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx counter nx))
      false false right).map (PSTRTMSeq005.rightCfg (a:=1) (b:=2))).length = _
  rw [List.length_append,List.length_map,List.length_map,scanTrace_length]
  change 2*dx.length+2+3 = _
  omega
theorem forwardNyTrace_length (sx : Bool) (counter nx dxTail right : List Bool) :
    (forwardNyTrace sx counter nx dxTail right).length=2*(nx.length+(false::dxTail).length)+15 := by
  change (((forwardDxTrace sx counter nx (true::(PSTRTMIncrement009.blocks dxTail++false::false::false::right))).map
      (PSTRTMSeq005.leftCfg (a:=9) (b:=4))) ++
    (forwardNyCoreTrace sx counter nx (false::dxTail) right).map (PSTRTMSeq005.rightCfg (a:=9) (b:=4))).length = _
  rw [List.length_append,List.length_map,List.length_map,forwardDxTrace_length,forwardNyCoreTrace_length]
  omega
theorem forwardDyTrace_length (sx : Bool) (counter nx dxTail ny tail : List Bool) :
    (forwardDyTrace sx counter nx dxTail ny tail).length=2*(nx.length+(false::dxTail).length+ny.length)+17 := by
  change (((forwardNyTrace sx counter nx dxTail (nxStream ny (false::tail))).map
      (PSTRTMSeq005.leftCfg (a:=14) (b:=1))) ++
    (scanTrace (false::nyContext sx counter nx (false::dxTail)) ny false tail).map
      (PSTRTMSeq005.rightCfg (a:=14) (b:=1))).length = _
  rw [List.length_append,List.length_map,List.length_map,forwardNyTrace_length,scanTrace_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
