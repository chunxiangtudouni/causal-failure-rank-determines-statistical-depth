module
public import Structure.PA17_TM_RatArithmetic_Bookmark_014c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
open PA17TMDivisionCompose006 PA17TMRatArithmeticParse002 PA17TMRatArithmeticFieldNav012

instance (stage : Fin 12) : Decidable (IsBack stage) :=
  inferInstanceAs (Decidable (stage.val=1 ∨ stage.val=3 ∨ stage.val=7 ∨ stage.val=9))

def mDy (y : Rat) : Fin 32 := saveBit 0 1 (observedFirst (denominatorDigits y))
def mNy (y : Rat) : Fin 32 := saveBit (mDy y) 2 (observedFirst (numeratorDigits y))
def mSign (y : Rat) : Fin 32 := saveBit (mNy y) 4 (sign y)
def mDx (x y : Rat) : Fin 32 := saveBit (mSign y) 8 (observedFirst (denominatorDigits x))
def mNx (x y : Rat) : Fin 32 := saveBit (mDx x y) 16 (observedFirst (numeratorDigits x))

def dyRight (y : Rat) : List Bool := PSTRTMIncrement009.blocks (clampFirst (denominatorDigits y))++[false,false,true]
def nyRight (y : Rat) : List Bool := PSTRTMIncrement009.blocks (clampFirst (numeratorDigits y))++false::dyRight y
def syRight (y : Rat) : List Bool := false::false::nyRight y
def dxRight (x y : Rat) : List Bool := PSTRTMIncrement009.blocks (clampFirst (denominatorDigits x))++false::syRight y
def nxRight (x y : Rat) : List Bool := PSTRTMIncrement009.blocks (clampFirst (numeratorDigits x))++false::dxRight x y

def tape0 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (pairLeft [] x y) [true]
def tape1 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (pairLeft [] x y) [false,true]
def tape2 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxDy [] x y)
  (PSTRTMIncrement009.blocks (denominatorDigits y)++[false,false,true])
def tape3 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxDy [] x y) (dyRight y)
def tape4 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxNy [] x y)
  (PSTRTMIncrement009.blocks (numeratorDigits y)++false::dyRight y)
def tape5 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxNy [] x y) (nyRight y)
def tape6 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (ratLeft (listPrefixLeft []) x) (sign y::false::nyRight y)
def tape7 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (ratLeft (listPrefixLeft []) x) (syRight y)
def tape8 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxDx [] x)
  (PSTRTMIncrement009.blocks (denominatorDigits x)++false::syRight y)
def tape9 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxDx [] x) (dxRight x y)
def tape10 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxNx [] x)
  (PSTRTMIncrement009.blocks (numeratorDigits x)++false::dxRight x y)
def tape11 (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxNx [] x) (nxRight x y)

def mark0 (x y : Rat) :
    Piece (memoryCfg 0 0 ⟨0,tape0 x y⟩)
      (memoryCfg 0 0 (padCfg (by decide : 4≤5) (markerState 4 (pairLeft [] x y) [false,true]))) :=
  (markerPiece 0 (pairLeft [] x y)).retarget
    (by simp only [markerState,pad_zero,tape0]) rfl

def back1 (x y : Rat) := backPiece 1 0 (ctxDy [] x y) (denominatorDigits y) [false,true] (by decide : IsBack 1)
def read2 (x y : Rat) :
    Piece (memoryCfg 2 0 ⟨0,tape2 x y⟩)
      (memoryCfg 2 0 (readEnd (observedFirst (denominatorDigits y)) (tape3 x y))) :=
  fieldReadPiece 2 0 (false::ctxDy [] x y) (denominatorDigits y) [false,false,true]
    (denominator_ne_nil y) (by decide)

def back3 (x y : Rat) := backPiece 3 (mDy y) (ctxNy [] x y) (numeratorDigits y) (dyRight y) (by decide : IsBack 3)
def read4 (x y : Rat) :
    Piece (memoryCfg 4 (mDy y) ⟨0,tape4 x y⟩)
      (memoryCfg 4 (mDy y) (readEnd (observedFirst (numeratorDigits y)) (tape5 x y))) :=
  fieldReadPiece 4 (mDy y) (false::ctxNy [] x y) (numeratorDigits y) (false::dyRight y)
    (numerator_ne_nil y) (by decide)

def back5 (x y : Rat) := headerPiece (mNy y) (ratLeft (listPrefixLeft []) x) false (sign y) (nyRight y)
def read6 (x y : Rat) :
    Piece (memoryCfg 6 (mNy y) ⟨0,tape6 x y⟩)
      (memoryCfg 6 (mNy y) (readEnd (sign y) (tape7 x y))) :=
  readPiece 6 (mNy y) (ratLeft (listPrefixLeft []) x) (sign y) (false::nyRight y) (by decide)

def back7 (x y : Rat) := backPiece 7 (mSign y) (ctxDx [] x) (denominatorDigits x) (syRight y) (by decide : IsBack 7)
def read8 (x y : Rat) :
    Piece (memoryCfg 8 (mSign y) ⟨0,tape8 x y⟩)
      (memoryCfg 8 (mSign y) (readEnd (observedFirst (denominatorDigits x)) (tape9 x y))) :=
  fieldReadPiece 8 (mSign y) (false::ctxDx [] x) (denominatorDigits x) (false::syRight y)
    (denominator_ne_nil x) (by decide)

def back9 (x y : Rat) := backPiece 9 (mDx x y) (ctxNx [] x) (numeratorDigits x) (dxRight x y) (by decide : IsBack 9)
def read10 (x y : Rat) :
    Piece (memoryCfg 10 (mDx x y) ⟨0,tape10 x y⟩)
      (memoryCfg 10 (mDx x y) (readEnd (observedFirst (numeratorDigits x)) (tape11 x y))) :=
  fieldReadPiece 10 (mDx x y) (false::ctxNx [] x) (numeratorDigits x) (false::dxRight x y)
    (numerator_ne_nil x) (by decide)

theorem transfer2 (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 2 0 (readEnd (observedFirst (denominatorDigits y)) (tape3 x y)))=
      some (memoryCfg 3 (mDy y) ⟨0,tape3 x y⟩) :=
  field_read_transfer 2 0 (false::ctxDy [] x y) (denominatorDigits y) [false,false,true] (by decide) (by decide)
theorem transfer4 (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 4 (mDy y) (readEnd (observedFirst (numeratorDigits y)) (tape5 x y)))=
      some (memoryCfg 5 (mNy y) ⟨0,tape5 x y⟩) :=
  field_read_transfer 4 (mDy y) (false::ctxNy [] x y) (numeratorDigits y) (false::dyRight y) (by decide) (by decide)
theorem transfer6 (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 6 (mNy y) (readEnd (sign y) (tape7 x y)))=
      some (memoryCfg 7 (mSign y) ⟨0,tape7 x y⟩) :=
  read_transfer 6 (mNy y) (ratLeft (listPrefixLeft []) x) (sign y) (false::nyRight y) (by decide) (by decide)
theorem transfer8 (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 8 (mSign y) (readEnd (observedFirst (denominatorDigits x)) (tape9 x y)))=
      some (memoryCfg 9 (mDx x y) ⟨0,tape9 x y⟩) :=
  field_read_transfer 8 (mSign y) (false::ctxDx [] x) (denominatorDigits x) (false::syRight y) (by decide) (by decide)
theorem transfer10 (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 10 (mDx x y) (readEnd (observedFirst (numeratorDigits x)) (tape11 x y)))=
      some (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  field_read_transfer 10 (mDx x y) (false::ctxNx [] x) (numeratorDigits x) (false::dxRight x y) (by decide) (by decide)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
