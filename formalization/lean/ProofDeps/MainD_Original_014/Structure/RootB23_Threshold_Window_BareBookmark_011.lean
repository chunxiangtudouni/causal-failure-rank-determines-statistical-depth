module

public import Structure.RootB23_Threshold_RoutedLoop_007

/-! The SAME frozen Bookmark014 program on the bare pair parser's arbitrary
WEST base. These are the original physical marker/read/rewind pieces, with
the actual base carried through their tape equations. There is no invented
list header, and observed bits remain in the program's actual finite port. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.BareBookmark
open Turing PSTRTMSeq005 PA17TMDivisionCompose006 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticFieldNav012 PA17TMRatArithmeticBookmark014
open PA17TMRatArithmeticWidth018 (BoundedRun)

def pairLeft (base : List Bool) (x y : Rat) : List Bool := ratLeft (ratLeft base x) y
def ctxNy (base : List Bool) (x y : Rat) : List Bool := sign y :: ratLeft base x
def ctxDy (base : List Bool) (x y : Rat) : List Bool :=
  PSTRTMRawNat010.leftBlocks (numeratorDigits y).reverse ++ false :: ctxNy base x y
def ctxNx (base : List Bool) (x : Rat) : List Bool := sign x :: base
def ctxDx (base : List Bool) (x : Rat) : List Bool :=
  PSTRTMRawNat010.leftBlocks (numeratorDigits x).reverse ++ false :: ctxNx base x

def tape0 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (pairLeft base x y) [true]
def tape1 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (pairLeft base x y) [false,true]
def tape2 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxDy base x y)
  (PSTRTMIncrement009.blocks (denominatorDigits y)++[false,false,true])
def tape3 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxDy base x y) (dyRight y)
def tape4 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxNy base x y)
  (PSTRTMIncrement009.blocks (numeratorDigits y)++false::dyRight y)
def tape5 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxNy base x y) (nyRight y)
def tape6 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (ratLeft base x) (sign y::false::nyRight y)
def tape7 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (ratLeft base x) (syRight y)
def tape8 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxDx base x)
  (PSTRTMIncrement009.blocks (denominatorDigits x)++false::syRight y)
def tape9 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxDx base x) (dxRight x y)
def tape10 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxNx base x)
  (PSTRTMIncrement009.blocks (numeratorDigits x)++false::dxRight x y)
def tape11 (base : List Bool) (x y : Rat) : Turing.Tape Bool := Turing.Tape.mk₂ (false::ctxNx base x) (nxRight x y)

def mark0 (base : List Bool) (x y : Rat) :
    Piece (memoryCfg 0 0 ⟨0,tape0 base x y⟩)
      (memoryCfg 0 0 (padCfg (by decide : 4≤5) (markerState 4 (pairLeft base x y) [false,true]))) :=
  (markerPiece 0 (pairLeft base x y)).retarget
    (by simp only [markerState,pad_zero,tape0]) rfl

def back1 (base : List Bool) (x y : Rat) := backPiece 1 0 (ctxDy base x y) (denominatorDigits y) [false,true] (by decide : IsBack 1)
def read2 (base : List Bool) (x y : Rat) :
    Piece (memoryCfg 2 0 ⟨0,tape2 base x y⟩)
      (memoryCfg 2 0 (readEnd (observedFirst (denominatorDigits y)) (tape3 base x y))) :=
  fieldReadPiece 2 0 (false::ctxDy base x y) (denominatorDigits y) [false,false,true]
    (denominator_ne_nil y) (by decide)

def back3 (base : List Bool) (x y : Rat) := backPiece 3 (mDy y) (ctxNy base x y) (numeratorDigits y) (dyRight y) (by decide : IsBack 3)
def read4 (base : List Bool) (x y : Rat) :
    Piece (memoryCfg 4 (mDy y) ⟨0,tape4 base x y⟩)
      (memoryCfg 4 (mDy y) (readEnd (observedFirst (numeratorDigits y)) (tape5 base x y))) :=
  fieldReadPiece 4 (mDy y) (false::ctxNy base x y) (numeratorDigits y) (false::dyRight y)
    (numerator_ne_nil y) (by decide)

def back5 (base : List Bool) (x y : Rat) := headerPiece (mNy y) (ratLeft base x) false (sign y) (nyRight y)
def read6 (base : List Bool) (x y : Rat) :
    Piece (memoryCfg 6 (mNy y) ⟨0,tape6 base x y⟩)
      (memoryCfg 6 (mNy y) (readEnd (sign y) (tape7 base x y))) :=
  readPiece 6 (mNy y) (ratLeft base x) (sign y) (false::nyRight y) (by decide)

def back7 (base : List Bool) (x y : Rat) := backPiece 7 (mSign y) (ctxDx base x) (denominatorDigits x) (syRight y) (by decide : IsBack 7)
def read8 (base : List Bool) (x y : Rat) :
    Piece (memoryCfg 8 (mSign y) ⟨0,tape8 base x y⟩)
      (memoryCfg 8 (mSign y) (readEnd (observedFirst (denominatorDigits x)) (tape9 base x y))) :=
  fieldReadPiece 8 (mSign y) (false::ctxDx base x) (denominatorDigits x) (false::syRight y)
    (denominator_ne_nil x) (by decide)

def back9 (base : List Bool) (x y : Rat) := backPiece 9 (mDx x y) (ctxNx base x) (numeratorDigits x) (dxRight x y) (by decide : IsBack 9)
def read10 (base : List Bool) (x y : Rat) :
    Piece (memoryCfg 10 (mDx x y) ⟨0,tape10 base x y⟩)
      (memoryCfg 10 (mDx x y) (readEnd (observedFirst (numeratorDigits x)) (tape11 base x y))) :=
  fieldReadPiece 10 (mDx x y) (false::ctxNx base x) (numeratorDigits x) (false::dxRight x y)
    (numerator_ne_nil x) (by decide)

theorem transfer2 (base : List Bool) (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 2 0 (readEnd (observedFirst (denominatorDigits y)) (tape3 base x y)))=
      some (memoryCfg 3 (mDy y) ⟨0,tape3 base x y⟩) :=
  field_read_transfer 2 0 (false::ctxDy base x y) (denominatorDigits y) [false,false,true] (by decide) (by decide)
theorem transfer4 (base : List Bool) (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 4 (mDy y) (readEnd (observedFirst (numeratorDigits y)) (tape5 base x y)))=
      some (memoryCfg 5 (mNy y) ⟨0,tape5 base x y⟩) :=
  field_read_transfer 4 (mDy y) (false::ctxNy base x y) (numeratorDigits y) (false::dyRight y) (by decide) (by decide)
theorem transfer6 (base : List Bool) (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 6 (mNy y) (readEnd (sign y) (tape7 base x y)))=
      some (memoryCfg 7 (mSign y) ⟨0,tape7 base x y⟩) :=
  read_transfer 6 (mNy y) (ratLeft base x) (sign y) (false::nyRight y) (by decide) (by decide)
theorem transfer8 (base : List Bool) (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 8 (mSign y) (readEnd (observedFirst (denominatorDigits x)) (tape9 base x y)))=
      some (memoryCfg 9 (mDx x y) ⟨0,tape9 base x y⟩) :=
  field_read_transfer 8 (mSign y) (false::ctxDx base x) (denominatorDigits x) (false::syRight y) (by decide) (by decide)
theorem transfer10 (base : List Bool) (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 10 (mDx x y) (readEnd (observedFirst (numeratorDigits x)) (tape11 base x y)))=
      some (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  field_read_transfer 10 (mDx x y) (false::ctxNx base x) (numeratorDigits x) (false::dxRight x y) (by decide) (by decide)


def from10 (base : List Bool) (x y : Rat) : Piece (memoryCfg 10 (mDx x y) ⟨0,tape10 base x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  (read10 base x y).join (donePiece (mNx x y) (tape11 base x y)) (transfer10 base x y)

def from9 (base : List Bool) (x y : Rat) : Piece
    (memoryCfg 9 (mDx x y) ⟨0,tape9 base x y⟩) (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  (back9 base x y).join (from10 base x y)
    (back_transfer 9 (mDx x y) (ctxNx base x) (numeratorDigits x) (dxRight x y)
      (by decide) (by decide) (by decide))

def from8 (base : List Bool) (x y : Rat) : Piece (memoryCfg 8 (mSign y) ⟨0,tape8 base x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  (read8 base x y).join (from9 base x y) (transfer8 base x y)

def from7 (base : List Bool) (x y : Rat) : Piece (memoryCfg 7 (mSign y) ⟨0,tape7 base x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  (back7 base x y).join (from8 base x y)
    (back_transfer 7 (mSign y) (ctxDx base x) (denominatorDigits x) (syRight y)
      (by decide) (by decide) (by decide))

def from6 (base : List Bool) (x y : Rat) : Piece (memoryCfg 6 (mNy y) ⟨0,tape6 base x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  (read6 base x y).join (from7 base x y) (transfer6 base x y)

theorem transfer5 (base : List Bool) (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 5 (mNy y) (padCfg (by decide : 2≤5)
      (headerState 2 (ratLeft base x) (sign y::false::nyRight y))))=
      some (memoryCfg 6 (mNy y) ⟨0,tape6 base x y⟩) := by
  apply quiet_transfer 5 (mNy y) _ (by decide) (by decide)
  exact (pad_runsFrom (by decide : 2≤5) headerBackMachine _ _ _
    (headerBack_runsFrom (ratLeft base x) false (sign y) (nyRight y))).2.2.2

def from5 (base : List Bool) (x y : Rat) : Piece (memoryCfg 5 (mNy y) ⟨0,tape5 base x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  ((back5 base x y).join (from6 base x y) (transfer5 base x y)).retarget
    (by simp only [headerState,pad_zero,tape5,ctxNy]) rfl

def from4 (base : List Bool) (x y : Rat) : Piece (memoryCfg 4 (mDy y) ⟨0,tape4 base x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  (read4 base x y).join (from5 base x y) (transfer4 base x y)

def from3 (base : List Bool) (x y : Rat) : Piece (memoryCfg 3 (mDy y) ⟨0,tape3 base x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  (back3 base x y).join (from4 base x y)
    (back_transfer 3 (mDy y) (ctxNy base x y) (numeratorDigits y) (dyRight y)
      (by decide) (by decide) (by decide))

def from2 (base : List Bool) (x y : Rat) : Piece (memoryCfg 2 0 ⟨0,tape2 base x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  (read2 base x y).join (from3 base x y) (transfer2 base x y)

def from1 (base : List Bool) (x y : Rat) : Piece (memoryCfg 1 0 ⟨0,tape1 base x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  (back1 base x y).join (from2 base x y)
    (back_transfer 1 0 (ctxDy base x y) (denominatorDigits y) [false,true]
      (by decide) (by decide) (by decide))

theorem transfer0 (base : List Bool) (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 0 0 (padCfg (by decide : 4≤5) (markerState 4 (pairLeft base x y) [false,true])))=
      some (memoryCfg 1 0 ⟨0,tape1 base x y⟩) := by
  apply quiet_transfer 0 0 _ (by decide) (by decide)
  exact (pad_runsFrom (by decide : 4≤5) markerMachine _ _ _ (marker_runsFrom (pairLeft base x y))).2.2.2

def completePiece (base : List Bool) (x y : Rat) : Piece (memoryCfg 0 0 ⟨0,tape0 base x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩) :=
  (mark0 base x y).join (from1 base x y) (transfer0 base x y)

def bookmarkTrace (base : List Bool) (x y : Rat) : List (MachineState 2303) := (completePiece base x y).trace
def bookmarkFinal (base : List Bool) (x y : Rat) : MachineState 2303 := memoryCfg 11 (mNx x y) ⟨0,tape11 base x y⟩

theorem initial_zero (tape : Turing.Tape Bool) : memoryCfg 0 0 ⟨0,tape⟩=(⟨0,tape⟩ : MachineState 2303) := by
  simp [memoryCfg,memoryPhase,blockCfg,label]
  rfl

/-- Fixed initial label0, all actual observed bits in finite control,
and the SAME exhibited chain through every read/clamp/transfer. -/
theorem bookmark_runsFrom (base : List Bool) (x y : Rat) : PSTRTMSeq005.RunsFrom bookmarkMachine
    ⟨0,tape0 base x y⟩ (bookmarkTrace base x y) (bookmarkFinal base x y) := by
  have h := segment_runsFrom bookmarkMachine _ _ _ (completePiece base x y).run (done_halt (mNx x y) (tape11 base x y))
  simpa only [initial_zero,bookmarkTrace,bookmarkFinal] using h

theorem bookmark_final_tape (base : List Bool) (x y : Rat) : (bookmarkFinal base x y).Tape=
    Turing.Tape.mk₂ (false::sign x::base) (nxRight x y) := rfl

theorem bookmark_final_memory (base : List Bool) (x y : Rat) :
    memoryOf (phaseOf (p:=383) (s:=5) (bookmarkFinal base x y).q)=mNx x y := by
  simp only [bookmarkFinal,memoryCfg,blockCfg,phaseOf_label,memoryOf_memoryPhase]


theorem from10_length (base : List Bool) (x y : Rat) : (from10 base x y).trace.length=3 := by
  have h : (from10 base x y).trace.length=(read10 base x y).trace.length+(donePiece (mNx x y) (tape11 base x y)).trace.length :=
    Piece.join_length (read10 base x y) (donePiece (mNx x y) (tape11 base x y)) (transfer10 base x y)
  have hr : (read10 base x y).trace.length=2 := fieldReadPiece_length 10 (mDx x y) (false::ctxNx base x)
    (numeratorDigits x) (false::dxRight x y) (numerator_ne_nil x) (by decide)
  rw [h,hr]
  rfl
theorem from9_length (base : List Bool) (x y : Rat) : (from9 base x y).trace.length=2*(numeratorDigits x).length+8 := by
  have h : (from9 base x y).trace.length=(back9 base x y).trace.length+(from10 base x y).trace.length :=
    Piece.join_length (back9 base x y) (from10 base x y)
      (back_transfer 9 (mDx x y) (ctxNx base x) (numeratorDigits x) (dxRight x y) (by decide) (by decide) (by decide))
  have hb : (back9 base x y).trace.length=2*(numeratorDigits x).length+5 :=
    backPiece_length 9 (mDx x y) (ctxNx base x) (numeratorDigits x) (dxRight x y) (by decide)
  rw [h,hb,from10_length]
theorem from8_length (base : List Bool) (x y : Rat) : (from8 base x y).trace.length=2*(numeratorDigits x).length+10 := by
  have h : (from8 base x y).trace.length=(read8 base x y).trace.length+(from9 base x y).trace.length :=
    Piece.join_length (read8 base x y) (from9 base x y) (transfer8 base x y)
  have hr : (read8 base x y).trace.length=2 := fieldReadPiece_length 8 (mSign y) (false::ctxDx base x)
    (denominatorDigits x) (false::syRight y) (denominator_ne_nil x) (by decide)
  rw [h,hr,from9_length]
  omega
theorem from7_length (base : List Bool) (x y : Rat) : (from7 base x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length)+15 := by
  have h : (from7 base x y).trace.length=(back7 base x y).trace.length+(from8 base x y).trace.length :=
    Piece.join_length (back7 base x y) (from8 base x y)
      (back_transfer 7 (mSign y) (ctxDx base x) (denominatorDigits x) (syRight y) (by decide) (by decide) (by decide))
  have hb : (back7 base x y).trace.length=2*(denominatorDigits x).length+5 :=
    backPiece_length 7 (mSign y) (ctxDx base x) (denominatorDigits x) (syRight y) (by decide)
  rw [h,hb,from8_length]
  omega
theorem from6_length (base : List Bool) (x y : Rat) : (from6 base x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length)+17 := by
  have h : (from6 base x y).trace.length=(read6 base x y).trace.length+(from7 base x y).trace.length :=
    Piece.join_length (read6 base x y) (from7 base x y) (transfer6 base x y)
  have hr : (read6 base x y).trace.length=2 := readPiece_length 6 (mNy y) (ratLeft base x)
    (sign y) (false::nyRight y) (by decide)
  rw [h,hr,from7_length]
  omega
theorem from5_length (base : List Bool) (x y : Rat) : (from5 base x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length)+20 := by
  have h : (from5 base x y).trace.length=(back5 base x y).trace.length+(from6 base x y).trace.length := by
    unfold from5
    rw [Piece.retarget_trace]
    exact Piece.join_length (back5 base x y) (from6 base x y) (transfer5 base x y)
  have hb : (back5 base x y).trace.length=3 := headerPiece_length (mNy y) (ratLeft base x)
    false (sign y) (nyRight y)
  rw [h,hb,from6_length]
  omega
theorem from4_length (base : List Bool) (x y : Rat) : (from4 base x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length)+22 := by
  have h : (from4 base x y).trace.length=(read4 base x y).trace.length+(from5 base x y).trace.length :=
    Piece.join_length (read4 base x y) (from5 base x y) (transfer4 base x y)
  have hr : (read4 base x y).trace.length=2 := fieldReadPiece_length 4 (mDy y) (false::ctxNy base x y)
    (numeratorDigits y) (false::dyRight y) (numerator_ne_nil y) (by decide)
  rw [h,hr,from5_length]
  omega
theorem from3_length (base : List Bool) (x y : Rat) : (from3 base x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length+(numeratorDigits y).length)+27 := by
  have h : (from3 base x y).trace.length=(back3 base x y).trace.length+(from4 base x y).trace.length :=
    Piece.join_length (back3 base x y) (from4 base x y)
      (back_transfer 3 (mDy y) (ctxNy base x y) (numeratorDigits y) (dyRight y) (by decide) (by decide) (by decide))
  have hb : (back3 base x y).trace.length=2*(numeratorDigits y).length+5 :=
    backPiece_length 3 (mDy y) (ctxNy base x y) (numeratorDigits y) (dyRight y) (by decide)
  rw [h,hb,from4_length]
  omega
theorem from2_length (base : List Bool) (x y : Rat) : (from2 base x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length+(numeratorDigits y).length)+29 := by
  have h : (from2 base x y).trace.length=(read2 base x y).trace.length+(from3 base x y).trace.length :=
    Piece.join_length (read2 base x y) (from3 base x y) (transfer2 base x y)
  have hr : (read2 base x y).trace.length=2 := fieldReadPiece_length 2 0 (false::ctxDy base x y)
    (denominatorDigits y) [false,false,true] (denominator_ne_nil y) (by decide)
  rw [h,hr,from3_length]
  omega
theorem from1_length (base : List Bool) (x y : Rat) : (from1 base x y).trace.length=2*fieldWidth x y+34 := by
  have h : (from1 base x y).trace.length=(back1 base x y).trace.length+(from2 base x y).trace.length :=
    Piece.join_length (back1 base x y) (from2 base x y)
      (back_transfer 1 0 (ctxDy base x y) (denominatorDigits y) [false,true] (by decide) (by decide) (by decide))
  have hb : (back1 base x y).trace.length=2*(denominatorDigits y).length+5 :=
    backPiece_length 1 0 (ctxDy base x y) (denominatorDigits y) [false,true] (by decide)
  rw [h,hb,from2_length]
  dsimp [fieldWidth]
  omega

/-- All eleven real finite-control transfer steps, five writes of observed
bits, marker allocation and four field rewinds are in this same trace. -/
theorem bookmarkTrace_length (base : List Bool) (x y : Rat) : (bookmarkTrace base x y).length=2*fieldWidth x y+39 := by
  have h : (completePiece base x y).trace.length=(mark0 base x y).trace.length+(from1 base x y).trace.length :=
    Piece.join_length (mark0 base x y) (from1 base x y) (transfer0 base x y)
  have hm : (mark0 base x y).trace.length=5 := by
    unfold mark0
    rw [Piece.retarget_trace]
    exact markerPiece_length 0 (pairLeft base x y)
  change (completePiece base x y).trace.length=_
  rw [h,hm,from1_length]
  omega


def bareMarkerMachine : Machine 1 := PA17TMRatArithmeticAllocate013.setMarkerMachine true

theorem bareMarker_bounded (base : List Bool) (x y : Rat) :
    BoundedRun bareMarkerMachine (Tape.mk₂ (pairLeft base x y) []) 1
      (Tape.mk₂ (pairLeft base x y) [true]) 2 := by
  have run := PA17TMRatArithmeticAllocate013.setMarker_runsFrom false true
    (pairLeft base x y) []
  have blank : Tape.mk₂ (pairLeft base x y) [false] = Tape.mk₂ (pairLeft base x y) [] := by
    simp only [Tape.mk₂, PSTRTMRawNat010.blank_single_false]
  simp only [PA17TMRatArithmeticAllocate013.seekState] at run
  rw [blank] at run
  exact ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false true (pairLeft base x y) [], run, by rfl⟩

def bareParseMarkerMachine : Machine 93 := seqMachine pairMachine bareMarkerMachine
def bareBookmarkMachine : Machine 2397 := seqMachine bareParseMarkerMachine bookmarkMachine

/-- Actual bare2Rat entry, real footer creation, and the existing symbol-
observing bookmark. Runtime widths and the saved tuple are not code inputs. -/
theorem bareBookmark_bounded (base : List Bool) (x y : Rat) :
    BoundedRun bareBookmarkMachine
      (Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y)))
      (rightLabel (a := 93) (bookmarkFinal base x y).q)
      (Tape.mk₂ (false :: sign x :: base) (nxRight x y))
      (32 * (fieldWidth x y + 1) ^ 2 + 2 * fieldWidth x y + 41) := by
  have parser : BoundedRun pairMachine
      (Tape.mk₂ base (encodeDatum (.rational x) ++ encodeDatum (.rational y)))
      (pairFinal base x y []).q (Tape.mk₂ (pairLeft base x y) [])
      (32 * (fieldWidth x y + 1) ^ 2) := by
    refine ⟨pairTrace base x y [], ?_, ?_⟩
    · have shape : pairFinal base x y [] =
          (⟨(pairFinal base x y []).q, Tape.mk₂ (pairLeft base x y) []⟩ : MachineState 91) := by
        cases h : pairFinal base x y [] with
        | mk q tape =>
          have tapeEq := pair_final_tape base x y []
          rw [h] at tapeEq
          exact congrArg (fun t => (⟨q, t⟩ : MachineState 91)) tapeEq
      have actual := pair_runsFrom base x y []
      rw [shape] at actual
      simpa only [List.append_nil] using actual
    · have old := originalParser_time x y
      rw [originalParserTrace_length] at old
      rw [pairTrace_length]
      unfold fieldWidth at old ⊢
      omega
  have bookmark : BoundedRun bookmarkMachine (Tape.mk₂ (pairLeft base x y) [true])
      (bookmarkFinal base x y).q (Tape.mk₂ (false :: sign x :: base) (nxRight x y))
      (2 * fieldWidth x y + 39) :=
    ⟨bookmarkTrace base x y, bookmark_runsFrom base x y, by rw [bookmarkTrace_length]⟩
  exact ((parser.seq (bareMarker_bounded base x y)).seq bookmark).mono (by omega)

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.BareBookmark
