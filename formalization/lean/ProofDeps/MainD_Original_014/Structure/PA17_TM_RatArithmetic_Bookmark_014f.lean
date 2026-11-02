module
public import Structure.PA17_TM_RatArithmetic_Bookmark_014e

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
open PA17TMDivisionCompose006 PA17TMRatArithmeticParse002 PA17TMRatArithmeticFieldNav012

def memoryCode (dy ny sy dx nx : Bool) : Fin 32 :=
  saveBit (saveBit (saveBit (saveBit (saveBit 0 1 dy) 2 ny) 4 sy) 8 dx) 16 nx

/-- Pure finite-control decoding only. No tape/state RHS is expanded into
thirty-two cases; these are five Boolean observations already made. -/
theorem memoryCode_bits (dy ny sy dx nx : Bool) :
    (memoryCode dy ny sy dx nx).val.testBit 0=dy ∧
    (memoryCode dy ny sy dx nx).val.testBit 1=ny ∧
    (memoryCode dy ny sy dx nx).val.testBit 2=sy ∧
    (memoryCode dy ny sy dx nx).val.testBit 3=dx ∧
    (memoryCode dy ny sy dx nx).val.testBit 4=nx := by
  cases dy <;> cases ny <;> cases sy <;> cases dx <;> cases nx <;> decide

theorem observed_memory_bits (x y : Rat) :
    (mNx x y).val.testBit 0=observedFirst (denominatorDigits y) ∧
    (mNx x y).val.testBit 1=observedFirst (numeratorDigits y) ∧
    (mNx x y).val.testBit 2=sign y ∧
    (mNx x y).val.testBit 3=observedFirst (denominatorDigits x) ∧
    (mNx x y).val.testBit 4=observedFirst (numeratorDigits x) :=
  memoryCode_bits (observedFirst (denominatorDigits y)) (observedFirst (numeratorDigits y))
    (sign y) (observedFirst (denominatorDigits x)) (observedFirst (numeratorDigits x))

def rawBookmarkMachine : Machine 2401 := PSTRTMSeq005.seqMachine originalParserMachine bookmarkMachine
def rawBookmarkTrace (x y : Rat) : List (MachineState 2401) :=
  (originalParserTrace x y).map (PSTRTMSeq005.leftCfg (b:=2303)) ++
    (bookmarkTrace x y).map (PSTRTMSeq005.rightCfg (a:=97))
def rawBookmarkFinal (x y : Rat) : MachineState 2401 := PSTRTMSeq005.rightCfg (a:=97) (bookmarkFinal x y)

/-- The program starts at numeric label0 on the ORIGINAL raw pair input.
The codec-proved blank, actual new marker, all five reads/clamps and real
finite-control transfers belong to this ONE fixed-machine run. -/
theorem rawBookmark_runs (x y : Rat) :
    Runs rawBookmarkMachine (encode [.rational x,.rational y]) (rawBookmarkTrace x y) (rawBookmarkFinal x y) :=
  PSTRTMSeq005.seq_runs originalParserMachine bookmarkMachine (encode [.rational x,.rational y])
    (originalParserFinal x y) (bookmarkFinal x y) (originalParserTrace x y) (bookmarkTrace x y)
    (originalParser_runs x y) (bookmark_runsFrom x y)

theorem rawBookmark_final_tape (x y : Rat) : (rawBookmarkFinal x y).Tape=
    Turing.Tape.mk₂ (false::sign x::listPrefixLeft []) (nxRight x y) := rfl

/-- Continuations must preserve this actual finite-control memory port;
resetting their entry to an unconditional0 would discard observed bits. -/
theorem rawBookmark_final_label (x y : Rat) :
    (rawBookmarkFinal x y).q.val=98+(11*32+(mNx x y).val)*6 := by
  simp [rawBookmarkFinal,PSTRTMSeq005.rightCfg,PSTRTMSeq005.rightLabel,bookmarkFinal,
    memoryCfg,blockCfg,label,memoryPhase]

theorem rawBookmarkTrace_length (x y : Rat) :
    (rawBookmarkTrace x y).length=(originalParserTrace x y).length+(bookmarkTrace x y).length := by
  change (((originalParserTrace x y).map (PSTRTMSeq005.leftCfg (a:=97) (b:=2303))) ++
    (bookmarkTrace x y).map (PSTRTMSeq005.rightCfg (a:=97) (b:=2303))).length = _
  rw [List.length_append,List.length_map,List.length_map]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
