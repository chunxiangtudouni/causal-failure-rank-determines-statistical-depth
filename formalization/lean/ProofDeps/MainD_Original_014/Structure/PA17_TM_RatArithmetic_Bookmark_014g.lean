module
public import Structure.PA17_TM_RatArithmetic_Bookmark_014f

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
open PA17TMDivisionCompose006 PA17TMRatArithmeticParse002 PA17TMRatArithmeticFieldNav012

/-- Value-level contract for a later REAL controlled write/copy. This is
not an uncharged restoration step of the machine proved in this package. -/
def restoredDigits (memory : Fin 32) (which : Nat) (clamped : List Bool) : List Bool :=
  memory.val.testBit which::clamped.tail

theorem restoredDigits_eq (memory : Fin 32) (which : Nat) (digits : List Bool)
    (hne : digits≠[]) (hbit : memory.val.testBit which=observedFirst digits) :
    restoredDigits memory which (clampFirst digits)=digits := by
  change memory.val.testBit which::digits.tail=digits
  rw [hbit]
  exact (digits_observedFirst digits hne).symm

theorem original_fields_restorable (x y : Rat) :
    restoredDigits (mNx x y) 0 (clampFirst (denominatorDigits y))=denominatorDigits y ∧
    restoredDigits (mNx x y) 1 (clampFirst (numeratorDigits y))=numeratorDigits y ∧
    (mNx x y).val.testBit 2=sign y ∧
    restoredDigits (mNx x y) 3 (clampFirst (denominatorDigits x))=denominatorDigits x ∧
    restoredDigits (mNx x y) 4 (clampFirst (numeratorDigits x))=numeratorDigits x := by
  obtain ⟨hd,hn,hs,hx,hxx⟩:=observed_memory_bits x y
  exact ⟨restoredDigits_eq _ _ _ (denominator_ne_nil y) hd,
    restoredDigits_eq _ _ _ (numerator_ne_nil y) hn,hs,
    restoredDigits_eq _ _ _ (denominator_ne_nil x) hx,
    restoredDigits_eq _ _ _ (numerator_ne_nil x) hxx⟩

theorem markerPiece_length (memory : Fin 32) (archive : List Bool) : (markerPiece memory archive).trace.length=5 := by
  change (((markerTrace archive).map (padCfg (by decide : 4≤5))).map (blockCfg (memoryPhase 0 memory))).length=5
  rw [List.length_map,List.length_map]
  rfl
theorem backPiece_length (stage : Fin 12) (memory : Fin 32) (archive digits suffix : List Bool) (hb : IsBack stage) :
    (backPiece stage memory archive digits suffix hb).trace.length=2*digits.length+5 := by
  change ((fieldBackTrace archive digits suffix).map (blockCfg (memoryPhase stage memory))).length=_
  rw [List.length_map,fieldBackTrace_length]
theorem headerPiece_length (memory : Fin 32) (archive : List Bool) (near far : Bool) (suffix : List Bool) :
    (headerPiece memory archive near far suffix).trace.length=3 := by
  change (((headerBackTrace archive near far suffix).map (padCfg (by decide : 2≤5))).map
    (blockCfg (memoryPhase 5 memory))).length=3
  rw [List.length_map,List.length_map]
  rfl
theorem readPiece_length (stage : Fin 12) (memory : Fin 32) (archive : List Bool) (bit : Bool) (suffix : List Bool)
    (hr : IsRead stage) : (readPiece stage memory archive bit suffix hr).trace.length=2 :=
  readBlockTrace_length stage memory archive bit suffix
theorem fieldReadPiece_length (stage : Fin 12) (memory : Fin 32) (archive digits suffix : List Bool)
    (hne : digits≠[]) (hr : IsRead stage) : (fieldReadPiece stage memory archive digits suffix hne hr).trace.length=2 := by
  simp only [fieldReadPiece,Piece.retarget_trace,readPiece_length]

theorem from10_length (x y : Rat) : (from10 x y).trace.length=3 := by
  have h : (from10 x y).trace.length=(read10 x y).trace.length+(donePiece (mNx x y) (tape11 x y)).trace.length :=
    Piece.join_length (read10 x y) (donePiece (mNx x y) (tape11 x y)) (transfer10 x y)
  have hr : (read10 x y).trace.length=2 := fieldReadPiece_length 10 (mDx x y) (false::ctxNx [] x)
    (numeratorDigits x) (false::dxRight x y) (numerator_ne_nil x) (by decide)
  rw [h,hr]
  rfl
theorem from9_length (x y : Rat) : (from9 x y).trace.length=2*(numeratorDigits x).length+8 := by
  have h : (from9 x y).trace.length=(back9 x y).trace.length+(from10 x y).trace.length :=
    Piece.join_length (back9 x y) (from10 x y)
      (back_transfer 9 (mDx x y) (ctxNx [] x) (numeratorDigits x) (dxRight x y) (by decide) (by decide) (by decide))
  have hb : (back9 x y).trace.length=2*(numeratorDigits x).length+5 :=
    backPiece_length 9 (mDx x y) (ctxNx [] x) (numeratorDigits x) (dxRight x y) (by decide)
  rw [h,hb,from10_length]
theorem from8_length (x y : Rat) : (from8 x y).trace.length=2*(numeratorDigits x).length+10 := by
  have h : (from8 x y).trace.length=(read8 x y).trace.length+(from9 x y).trace.length :=
    Piece.join_length (read8 x y) (from9 x y) (transfer8 x y)
  have hr : (read8 x y).trace.length=2 := fieldReadPiece_length 8 (mSign y) (false::ctxDx [] x)
    (denominatorDigits x) (false::syRight y) (denominator_ne_nil x) (by decide)
  rw [h,hr,from9_length]
  omega
theorem from7_length (x y : Rat) : (from7 x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length)+15 := by
  have h : (from7 x y).trace.length=(back7 x y).trace.length+(from8 x y).trace.length :=
    Piece.join_length (back7 x y) (from8 x y)
      (back_transfer 7 (mSign y) (ctxDx [] x) (denominatorDigits x) (syRight y) (by decide) (by decide) (by decide))
  have hb : (back7 x y).trace.length=2*(denominatorDigits x).length+5 :=
    backPiece_length 7 (mSign y) (ctxDx [] x) (denominatorDigits x) (syRight y) (by decide)
  rw [h,hb,from8_length]
  omega
theorem from6_length (x y : Rat) : (from6 x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length)+17 := by
  have h : (from6 x y).trace.length=(read6 x y).trace.length+(from7 x y).trace.length :=
    Piece.join_length (read6 x y) (from7 x y) (transfer6 x y)
  have hr : (read6 x y).trace.length=2 := readPiece_length 6 (mNy y) (ratLeft (listPrefixLeft []) x)
    (sign y) (false::nyRight y) (by decide)
  rw [h,hr,from7_length]
  omega
theorem from5_length (x y : Rat) : (from5 x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length)+20 := by
  have h : (from5 x y).trace.length=(back5 x y).trace.length+(from6 x y).trace.length := by
    unfold from5
    rw [Piece.retarget_trace]
    exact Piece.join_length (back5 x y) (from6 x y) (transfer5 x y)
  have hb : (back5 x y).trace.length=3 := headerPiece_length (mNy y) (ratLeft (listPrefixLeft []) x)
    false (sign y) (nyRight y)
  rw [h,hb,from6_length]
  omega
theorem from4_length (x y : Rat) : (from4 x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length)+22 := by
  have h : (from4 x y).trace.length=(read4 x y).trace.length+(from5 x y).trace.length :=
    Piece.join_length (read4 x y) (from5 x y) (transfer4 x y)
  have hr : (read4 x y).trace.length=2 := fieldReadPiece_length 4 (mDy y) (false::ctxNy [] x y)
    (numeratorDigits y) (false::dyRight y) (numerator_ne_nil y) (by decide)
  rw [h,hr,from5_length]
  omega
theorem from3_length (x y : Rat) : (from3 x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length+(numeratorDigits y).length)+27 := by
  have h : (from3 x y).trace.length=(back3 x y).trace.length+(from4 x y).trace.length :=
    Piece.join_length (back3 x y) (from4 x y)
      (back_transfer 3 (mDy y) (ctxNy [] x y) (numeratorDigits y) (dyRight y) (by decide) (by decide) (by decide))
  have hb : (back3 x y).trace.length=2*(numeratorDigits y).length+5 :=
    backPiece_length 3 (mDy y) (ctxNy [] x y) (numeratorDigits y) (dyRight y) (by decide)
  rw [h,hb,from4_length]
  omega
theorem from2_length (x y : Rat) : (from2 x y).trace.length=
    2*((numeratorDigits x).length+(denominatorDigits x).length+(numeratorDigits y).length)+29 := by
  have h : (from2 x y).trace.length=(read2 x y).trace.length+(from3 x y).trace.length :=
    Piece.join_length (read2 x y) (from3 x y) (transfer2 x y)
  have hr : (read2 x y).trace.length=2 := fieldReadPiece_length 2 0 (false::ctxDy [] x y)
    (denominatorDigits y) [false,false,true] (denominator_ne_nil y) (by decide)
  rw [h,hr,from3_length]
  omega
theorem from1_length (x y : Rat) : (from1 x y).trace.length=2*fieldWidth x y+34 := by
  have h : (from1 x y).trace.length=(back1 x y).trace.length+(from2 x y).trace.length :=
    Piece.join_length (back1 x y) (from2 x y)
      (back_transfer 1 0 (ctxDy [] x y) (denominatorDigits y) [false,true] (by decide) (by decide) (by decide))
  have hb : (back1 x y).trace.length=2*(denominatorDigits y).length+5 :=
    backPiece_length 1 0 (ctxDy [] x y) (denominatorDigits y) [false,true] (by decide)
  rw [h,hb,from2_length]
  dsimp [fieldWidth]
  omega

/-- All eleven real finite-control transfer steps, five writes of observed
bits, marker allocation and four field rewinds are in this same trace. -/
theorem bookmarkTrace_length (x y : Rat) : (bookmarkTrace x y).length=2*fieldWidth x y+39 := by
  have h : (completePiece x y).trace.length=(mark0 x y).trace.length+(from1 x y).trace.length :=
    Piece.join_length (mark0 x y) (from1 x y) (transfer0 x y)
  have hm : (mark0 x y).trace.length=5 := by
    unfold mark0
    rw [Piece.retarget_trace]
    exact markerPiece_length 0 (pairLeft [] x y)
  change (completePiece x y).trace.length=_
  rw [h,hm,from1_length]
  omega

theorem rawBookmark_time (x y : Rat) : (rawBookmarkTrace x y).length ≤ 128*(fieldWidth x y+1)^2 := by
  rw [rawBookmarkTrace_length,bookmarkTrace_length]
  have h:=originalParser_time x y
  nlinarith [Nat.zero_le ((fieldWidth x y)^2)]

theorem rawBookmark_space (x y : Rat) :
    visitedSpace rawBookmarkMachine (encode [.rational x,.rational y]).length (rawBookmarkTrace x y) ≤
      512*(fieldWidth x y+1)^2 := by
  have h:=PSTRTMTrace002.visitedSpace_le rawBookmarkMachine (encode [.rational x,.rational y]).length (rawBookmarkTrace x y)
  have ht:=rawBookmark_time x y
  have hw : (encode [.rational x,.rational y]).length=2*fieldWidth x y+14 := pair_length x y
  rw [hw] at h ⊢
  nlinarith [Nat.zero_le ((fieldWidth x y)^2)]

/-- Uniform constants on original raw input length; no caller budget,
width or saved-bit tuple is an input to either fixed program. -/
theorem original_input_cost (x y : Rat) :
    (rawBookmarkTrace x y).length ≤ 512*((encode [.rational x,.rational y]).length+1)^2 ∧
    visitedSpace rawBookmarkMachine (encode [.rational x,.rational y]).length (rawBookmarkTrace x y) ≤
      512*((encode [.rational x,.rational y]).length+1)^2 := by
  have ht:=rawBookmark_time x y
  have hs:=rawBookmark_space x y
  have hw : (encode [.rational x,.rational y]).length=2*fieldWidth x y+14 := pair_length x y
  rw [hw] at hs ⊢
  constructor <;> nlinarith [Nat.zero_le ((fieldWidth x y)^2)]

theorem original_bookmark_exists :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ trace final,
        Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=Turing.Tape.mk₂ (false::sign x::listPrefixLeft []) (nxRight x y) ∧
        final.q.val=98+(11*32+(mNx x y).val)*6 ∧
        trace.length ≤ c*((encode [.rational x,.rational y]).length+1)^d ∧
        visitedSpace program (encode [.rational x,.rational y]).length trace ≤
          c*((encode [.rational x,.rational y]).length+1)^d := by
  refine ⟨2401,512,2,rawBookmarkMachine,by decide,by decide,?_⟩
  intro x y
  exact ⟨rawBookmarkTrace x y,rawBookmarkFinal x y,rawBookmark_runs x y,rawBookmark_final_tape x y,
    rawBookmark_final_label x y,(original_input_cost x y).1,(original_input_cost x y).2⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
