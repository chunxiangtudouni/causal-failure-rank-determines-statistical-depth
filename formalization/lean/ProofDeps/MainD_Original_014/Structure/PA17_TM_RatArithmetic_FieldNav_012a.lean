module
public import Structure.PA17_TM_RatArithmetic_Parse_002g

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFieldNav012
open PA17TMRatArithmeticParse002

def pairLeft (base : List Bool) (x y : Rat) : List Bool := ratLeft (ratLeft (listPrefixLeft base) x) y
def ctxNy (base : List Bool) (x y : Rat) : List Bool := sign y::ratLeft (listPrefixLeft base) x
def ctxDy (base : List Bool) (x y : Rat) : List Bool :=
  PSTRTMRawNat010.leftBlocks (numeratorDigits y).reverse++false::ctxNy base x y
def ctxNx (base : List Bool) (x : Rat) : List Bool := sign x::listPrefixLeft base
def ctxDx (base : List Bool) (x : Rat) : List Bool :=
  PSTRTMRawNat010.leftBlocks (numeratorDigits x).reverse++false::ctxNx base x

def rightDy (y : Rat) (suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks (denominatorDigits y)++false::true::suffix
def rightNy (y : Rat) (suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks (numeratorDigits y)++false::rightDy y suffix
def rightDx (x y : Rat) (suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks (denominatorDigits x)++false::sign y::false::rightNy y suffix
def rightNx (x y : Rat) (suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks (numeratorDigits x)++false::rightDx x y suffix

def dyMachine : Machine 5 := fieldBackMachine
def dyTrace (base : List Bool) (x y : Rat) (suffix : List Bool) : List (MachineState 5) :=
  fieldBackTrace (ctxDy base x y) (denominatorDigits y) (true::suffix)
def dyFinal (base : List Bool) (x y : Rat) (suffix : List Bool) : MachineState 5 :=
  fieldBackFinal (ctxDy base x y) (denominatorDigits y) (true::suffix)

theorem dy_runsFrom (base : List Bool) (x y : Rat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom dyMachine ⟨0,Turing.Tape.mk₂ (pairLeft base x y) (true::suffix)⟩
      (dyTrace base x y suffix) (dyFinal base x y suffix) := by
  have h := fieldBack_runsFrom (ctxDy base x y) (denominatorDigits y) (true::suffix)
  simpa only [dyMachine,dyTrace,dyFinal,pairLeft,ctxDy,ctxNy,ratLeft,bothLeft,firstLeft] using h

theorem dy_final_tape (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (dyFinal base x y suffix).Tape = Turing.Tape.mk₂ (false::ctxDy base x y) (rightDy y suffix) := rfl

theorem dyTrace_length (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (dyTrace base x y suffix).length = 2*(denominatorDigits y).length+5 :=
  fieldBackTrace_length (ctxDy base x y) (denominatorDigits y) (true::suffix)

def nyMachine : Machine 11 := PSTRTMSeq005.seqMachine dyMachine fieldBackMachine
def nyTrace (base : List Bool) (x y : Rat) (suffix : List Bool) : List (MachineState 11) :=
  (dyTrace base x y suffix).map (PSTRTMSeq005.leftCfg (b:=5)) ++
    (fieldBackTrace (ctxNy base x y) (numeratorDigits y) (rightDy y suffix)).map (PSTRTMSeq005.rightCfg (a:=5))
def nyFinal (base : List Bool) (x y : Rat) (suffix : List Bool) : MachineState 11 :=
  PSTRTMSeq005.rightCfg (a:=5) (fieldBackFinal (ctxNy base x y) (numeratorDigits y) (rightDy y suffix))

theorem ny_runsFrom (base : List Bool) (x y : Rat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom nyMachine ⟨0,Turing.Tape.mk₂ (pairLeft base x y) (true::suffix)⟩
      (nyTrace base x y suffix) (nyFinal base x y suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom dyMachine fieldBackMachine
    (⟨0,Turing.Tape.mk₂ (pairLeft base x y) (true::suffix)⟩) (dyFinal base x y suffix)
    (fieldBackFinal (ctxNy base x y) (numeratorDigits y) (rightDy y suffix))
    (dyTrace base x y suffix) (fieldBackTrace (ctxNy base x y) (numeratorDigits y) (rightDy y suffix))
    (dy_runsFrom base x y suffix)
    (fieldBack_runsFrom (ctxNy base x y) (numeratorDigits y) (rightDy y suffix))
  simpa only [nyMachine,nyTrace,nyFinal,PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,
    Fin.val_zero,Fin.mk_zero] using h

theorem ny_final_tape (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (nyFinal base x y suffix).Tape = Turing.Tape.mk₂ (false::ctxNy base x y) (rightNy y suffix) := rfl

theorem nyTrace_length (base : List Bool) (x y : Rat) (suffix : List Bool) :
    (nyTrace base x y suffix).length =
      2*((denominatorDigits y).length+(numeratorDigits y).length)+10 := by
  change (((dyTrace base x y suffix).map (PSTRTMSeq005.leftCfg (a:=5) (b:=5))) ++
    (fieldBackTrace (ctxNy base x y) (numeratorDigits y) (rightDy y suffix)).map
      (PSTRTMSeq005.rightCfg (a:=5) (b:=5))).length = _
  rw [List.length_append,List.length_map,List.length_map,dyTrace_length,fieldBackTrace_length]
  omega

def headerBackMachine : Machine 2 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.move .left)
  | _ => none
def headerState (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩
def headerBackTrace (base : List Bool) (near far : Bool) (right : List Bool) : List (MachineState 2) :=
  [headerState 0 (near::far::base) right,headerState 1 (far::base) (near::right),
   headerState 2 base (far::near::right)]

theorem headerBack_runsFrom (base : List Bool) (near far : Bool) (right : List Bool) :
    PSTRTMSeq005.RunsFrom headerBackMachine (headerState 0 (near::far::base) right)
      (headerBackTrace base near far right) (headerState 2 base (far::near::right)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [headerBackTrace,List.isChain_cons_cons,Turing.TM0.step,headerBackMachine,headerState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,headerBackMachine,headerState]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFieldNav012
