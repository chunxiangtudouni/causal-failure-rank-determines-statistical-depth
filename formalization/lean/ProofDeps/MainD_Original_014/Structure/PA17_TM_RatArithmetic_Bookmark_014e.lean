module
public import Structure.PA17_TM_RatArithmetic_Bookmark_014d

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
open PA17TMDivisionCompose006 PA17TMRatArithmeticParse002 PA17TMRatArithmeticFieldNav012

theorem back_transfer (stage : Fin 12) (memory : Fin 32) (archive digits suffix : List Bool)
    (hb : IsBack stage) (hnext : stage.val<11) (hnr : ¬IsRead stage) :
    Turing.TM0.step bookmarkMachine (memoryCfg stage memory (fieldBackFinal archive digits suffix))=
      some (memoryCfg (nextStage stage hnext) memory ⟨0,(fieldBackFinal archive digits suffix).Tape⟩) := by
  apply quiet_transfer stage memory _ hnext hnr
  rw [stage_back stage hb]
  exact (fieldBack_runsFrom archive digits suffix).2.2.2

def from10 (x y : Rat) : Piece (memoryCfg 10 (mDx x y) ⟨0,tape10 x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  (read10 x y).join (donePiece (mNx x y) (tape11 x y)) (transfer10 x y)

def from9 (x y : Rat) : Piece
    (memoryCfg 9 (mDx x y) ⟨0,tape9 x y⟩) (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  (back9 x y).join (from10 x y)
    (back_transfer 9 (mDx x y) (ctxNx [] x) (numeratorDigits x) (dxRight x y)
      (by decide) (by decide) (by decide))

def from8 (x y : Rat) : Piece (memoryCfg 8 (mSign y) ⟨0,tape8 x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  (read8 x y).join (from9 x y) (transfer8 x y)

def from7 (x y : Rat) : Piece (memoryCfg 7 (mSign y) ⟨0,tape7 x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  (back7 x y).join (from8 x y)
    (back_transfer 7 (mSign y) (ctxDx [] x) (denominatorDigits x) (syRight y)
      (by decide) (by decide) (by decide))

def from6 (x y : Rat) : Piece (memoryCfg 6 (mNy y) ⟨0,tape6 x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  (read6 x y).join (from7 x y) (transfer6 x y)

theorem transfer5 (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 5 (mNy y) (padCfg (by decide : 2≤5)
      (headerState 2 (ratLeft (listPrefixLeft []) x) (sign y::false::nyRight y))))=
      some (memoryCfg 6 (mNy y) ⟨0,tape6 x y⟩) := by
  apply quiet_transfer 5 (mNy y) _ (by decide) (by decide)
  exact (pad_runsFrom (by decide : 2≤5) headerBackMachine _ _ _
    (headerBack_runsFrom (ratLeft (listPrefixLeft []) x) false (sign y) (nyRight y))).2.2.2

def from5 (x y : Rat) : Piece (memoryCfg 5 (mNy y) ⟨0,tape5 x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  ((back5 x y).join (from6 x y) (transfer5 x y)).retarget
    (by simp only [headerState,pad_zero,tape5,ctxNy]) rfl

def from4 (x y : Rat) : Piece (memoryCfg 4 (mDy y) ⟨0,tape4 x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  (read4 x y).join (from5 x y) (transfer4 x y)

def from3 (x y : Rat) : Piece (memoryCfg 3 (mDy y) ⟨0,tape3 x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  (back3 x y).join (from4 x y)
    (back_transfer 3 (mDy y) (ctxNy [] x y) (numeratorDigits y) (dyRight y)
      (by decide) (by decide) (by decide))

def from2 (x y : Rat) : Piece (memoryCfg 2 0 ⟨0,tape2 x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  (read2 x y).join (from3 x y) (transfer2 x y)

def from1 (x y : Rat) : Piece (memoryCfg 1 0 ⟨0,tape1 x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  (back1 x y).join (from2 x y)
    (back_transfer 1 0 (ctxDy [] x y) (denominatorDigits y) [false,true]
      (by decide) (by decide) (by decide))

theorem transfer0 (x y : Rat) : Turing.TM0.step bookmarkMachine
    (memoryCfg 0 0 (padCfg (by decide : 4≤5) (markerState 4 (pairLeft [] x y) [false,true])))=
      some (memoryCfg 1 0 ⟨0,tape1 x y⟩) := by
  apply quiet_transfer 0 0 _ (by decide) (by decide)
  exact (pad_runsFrom (by decide : 4≤5) markerMachine _ _ _ (marker_runsFrom (pairLeft [] x y))).2.2.2

def completePiece (x y : Rat) : Piece (memoryCfg 0 0 ⟨0,tape0 x y⟩)
    (memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩) :=
  (mark0 x y).join (from1 x y) (transfer0 x y)

def bookmarkTrace (x y : Rat) : List (MachineState 2303) := (completePiece x y).trace
def bookmarkFinal (x y : Rat) : MachineState 2303 := memoryCfg 11 (mNx x y) ⟨0,tape11 x y⟩

theorem initial_zero (tape : Turing.Tape Bool) : memoryCfg 0 0 ⟨0,tape⟩=(⟨0,tape⟩ : MachineState 2303) := by
  simp [memoryCfg,memoryPhase,blockCfg,label]

/-- Fixed initial label0, all actual observed bits in finite control,
and the SAME exhibited chain through every read/clamp/transfer. -/
theorem bookmark_runsFrom (x y : Rat) : PSTRTMSeq005.RunsFrom bookmarkMachine
    ⟨0,tape0 x y⟩ (bookmarkTrace x y) (bookmarkFinal x y) := by
  have h := segment_runsFrom bookmarkMachine _ _ _ (completePiece x y).run (done_halt (mNx x y) (tape11 x y))
  simpa only [initial_zero,bookmarkTrace,bookmarkFinal] using h

theorem bookmark_final_tape (x y : Rat) : (bookmarkFinal x y).Tape=
    Turing.Tape.mk₂ (false::sign x::listPrefixLeft []) (nxRight x y) := rfl

theorem bookmark_final_memory (x y : Rat) :
    memoryOf (phaseOf (p:=383) (s:=5) (bookmarkFinal x y).q)=mNx x y := by
  simp only [bookmarkFinal,memoryCfg,blockCfg,phaseOf_label,memoryOf_memoryPhase]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
