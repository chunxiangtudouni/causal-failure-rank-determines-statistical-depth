module
public import Structure.PA17_TM_RatArithmetic_FieldNav_012a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFieldNav012
open PA17TMRatArithmeticParse002

def headerDxMachine : Machine 8 := PSTRTMSeq005.seqMachine headerBackMachine fieldBackMachine
def headerDxTrace (base : List Bool) (x y : Rat) (suffix : List Bool) : List (MachineState 8) :=
  (headerBackTrace (ratLeft (listPrefixLeft base) x) false (sign y) (rightNy y suffix)).map
      (PSTRTMSeq005.leftCfg (b:=5)) ++
    (fieldBackTrace (ctxDx base x) (denominatorDigits x) (sign y::false::rightNy y suffix)).map
      (PSTRTMSeq005.rightCfg (a:=2))
def headerDxFinal (base : List Bool) (x y : Rat) (suffix : List Bool) : MachineState 8 :=
  PSTRTMSeq005.rightCfg (a:=2)
    (fieldBackFinal (ctxDx base x) (denominatorDigits x) (sign y::false::rightNy y suffix))

theorem headerDx_runsFrom (base : List Bool) (x y : Rat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom headerDxMachine ⟨0,Turing.Tape.mk₂ (false::ctxNy base x y) (rightNy y suffix)⟩
      (headerDxTrace base x y suffix) (headerDxFinal base x y suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom headerBackMachine fieldBackMachine
    (headerState 0 (false::sign y::ratLeft (listPrefixLeft base) x) (rightNy y suffix))
    (headerState 2 (ratLeft (listPrefixLeft base) x) (sign y::false::rightNy y suffix))
    (fieldBackFinal (ctxDx base x) (denominatorDigits x) (sign y::false::rightNy y suffix))
    (headerBackTrace (ratLeft (listPrefixLeft base) x) false (sign y) (rightNy y suffix))
    (fieldBackTrace (ctxDx base x) (denominatorDigits x) (sign y::false::rightNy y suffix))
    (headerBack_runsFrom (ratLeft (listPrefixLeft base) x) false (sign y) (rightNy y suffix))
    (fieldBack_runsFrom (ctxDx base x) (denominatorDigits x) (sign y::false::rightNy y suffix))
  simpa only [headerDxMachine,headerDxTrace,headerDxFinal,headerState,ctxNy,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem headerDxTrace_length (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (headerDxTrace base x y suffix).length = 2*(denominatorDigits x).length+8 := by
  change (((headerBackTrace (ratLeft (listPrefixLeft base) x) false (sign y) (rightNy y suffix)).map
      (PSTRTMSeq005.leftCfg (a:=2) (b:=5))) ++
    (fieldBackTrace (ctxDx base x) (denominatorDigits x) (sign y::false::rightNy y suffix)).map
      (PSTRTMSeq005.rightCfg (a:=2) (b:=5))).length = _
  rw [List.length_append,List.length_map,List.length_map,fieldBackTrace_length]
  change 3+(2*(denominatorDigits x).length+5) = _
  omega

def dxMachine : Machine 20 := PSTRTMSeq005.seqMachine nyMachine headerDxMachine
def dxTrace (base : List Bool) (x y : Rat) (suffix : List Bool) : List (MachineState 20) :=
  (nyTrace base x y suffix).map (PSTRTMSeq005.leftCfg (b:=8)) ++
    (headerDxTrace base x y suffix).map (PSTRTMSeq005.rightCfg (a:=11))
def dxFinal (base : List Bool) (x y : Rat) (suffix : List Bool) : MachineState 20 :=
  PSTRTMSeq005.rightCfg (a:=11) (headerDxFinal base x y suffix)

theorem dx_runsFrom (base : List Bool) (x y : Rat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom dxMachine ⟨0,Turing.Tape.mk₂ (pairLeft base x y) (true::suffix)⟩
      (dxTrace base x y suffix) (dxFinal base x y suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom nyMachine headerDxMachine
    (⟨0,Turing.Tape.mk₂ (pairLeft base x y) (true::suffix)⟩) (nyFinal base x y suffix)
    (headerDxFinal base x y suffix) (nyTrace base x y suffix) (headerDxTrace base x y suffix)
    (ny_runsFrom base x y suffix) (headerDx_runsFrom base x y suffix)
  simpa only [dxMachine,dxTrace,dxFinal,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,
    Fin.val_zero,Fin.mk_zero] using h

theorem dx_final_tape (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (dxFinal base x y suffix).Tape = Turing.Tape.mk₂ (false::ctxDx base x) (rightDx x y suffix) := rfl

theorem dxTrace_length (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (dxTrace base x y suffix).length =
      2*((denominatorDigits y).length+(numeratorDigits y).length+(denominatorDigits x).length)+18 := by
  change (((nyTrace base x y suffix).map (PSTRTMSeq005.leftCfg (a:=11) (b:=8))) ++
    (headerDxTrace base x y suffix).map (PSTRTMSeq005.rightCfg (a:=11) (b:=8))).length = _
  rw [List.length_append,List.length_map,List.length_map,nyTrace_length,headerDxTrace_length]
  omega

def nxMachine : Machine 26 := PSTRTMSeq005.seqMachine dxMachine fieldBackMachine
def nxTrace (base : List Bool) (x y : Rat) (suffix : List Bool) : List (MachineState 26) :=
  (dxTrace base x y suffix).map (PSTRTMSeq005.leftCfg (b:=5)) ++
    (fieldBackTrace (ctxNx base x) (numeratorDigits x) (rightDx x y suffix)).map (PSTRTMSeq005.rightCfg (a:=20))
def nxFinal (base : List Bool) (x y : Rat) (suffix : List Bool) : MachineState 26 :=
  PSTRTMSeq005.rightCfg (a:=20) (fieldBackFinal (ctxNx base x) (numeratorDigits x) (rightDx x y suffix))

theorem nx_runsFrom (base : List Bool) (x y : Rat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom nxMachine ⟨0,Turing.Tape.mk₂ (pairLeft base x y) (true::suffix)⟩
      (nxTrace base x y suffix) (nxFinal base x y suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom dxMachine fieldBackMachine
    (⟨0,Turing.Tape.mk₂ (pairLeft base x y) (true::suffix)⟩) (dxFinal base x y suffix)
    (fieldBackFinal (ctxNx base x) (numeratorDigits x) (rightDx x y suffix))
    (dxTrace base x y suffix) (fieldBackTrace (ctxNx base x) (numeratorDigits x) (rightDx x y suffix))
    (dx_runsFrom base x y suffix) (fieldBack_runsFrom (ctxNx base x) (numeratorDigits x) (rightDx x y suffix))
  simpa only [nxMachine,nxTrace,nxFinal,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,
    Fin.val_zero,Fin.mk_zero] using h

theorem nx_final_tape (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (nxFinal base x y suffix).Tape = Turing.Tape.mk₂ (false::ctxNx base x) (rightNx x y suffix) := rfl

theorem nxTrace_length (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (nxTrace base x y suffix).length = 2*fieldWidth x y+23 := by
  change (((dxTrace base x y suffix).map (PSTRTMSeq005.leftCfg (a:=20) (b:=5))) ++
    (fieldBackTrace (ctxNx base x) (numeratorDigits x) (rightDx x y suffix)).map
      (PSTRTMSeq005.rightCfg (a:=20) (b:=5))).length = _
  rw [List.length_append,List.length_map,List.length_map,dxTrace_length,fieldBackTrace_length]
  dsimp [fieldWidth]
  omega

/-- Four distinct fixed programs; the desired field is compiled in code,
not supplied as a numeric index/length/oracle on the input tape. -/
theorem four_trace_bounds (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (dyTrace base x y suffix).length ≤ 2*fieldWidth x y+23 ∧
    (nyTrace base x y suffix).length ≤ 2*fieldWidth x y+23 ∧
    (dxTrace base x y suffix).length ≤ 2*fieldWidth x y+23 ∧
    (nxTrace base x y suffix).length ≤ 2*fieldWidth x y+23 := by
  rw [dyTrace_length,nyTrace_length,dxTrace_length,nxTrace_length]
  dsimp [fieldWidth]
  omega

theorem four_space_bounds (inputLength : Nat) (base : List Bool) (x y : Rat) (suffix : List Bool) :
    visitedSpace dyMachine inputLength (dyTrace base x y suffix) ≤ inputLength+4*fieldWidth x y+47 ∧
    visitedSpace nyMachine inputLength (nyTrace base x y suffix) ≤ inputLength+4*fieldWidth x y+47 ∧
    visitedSpace dxMachine inputLength (dxTrace base x y suffix) ≤ inputLength+4*fieldWidth x y+47 ∧
    visitedSpace nxMachine inputLength (nxTrace base x y suffix) ≤ inputLength+4*fieldWidth x y+47 := by
  have hd := PSTRTMTrace002.visitedSpace_le dyMachine inputLength (dyTrace base x y suffix)
  have hn := PSTRTMTrace002.visitedSpace_le nyMachine inputLength (nyTrace base x y suffix)
  have hx := PSTRTMTrace002.visitedSpace_le dxMachine inputLength (dxTrace base x y suffix)
  have hnx := PSTRTMTrace002.visitedSpace_le nxMachine inputLength (nxTrace base x y suffix)
  have h := four_trace_bounds base x y suffix
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFieldNav012
