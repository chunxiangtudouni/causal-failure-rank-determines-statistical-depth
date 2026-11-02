module
public import Structure.PA17_TM_RatArithmetic_Width_018a

/-! Return across the current field's physically cleared flag. Rewind
first stops at that marker, two real LEFT steps cross marker and data,
and the second rewind traverses only the earlier still-flagged earlier. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticFieldNav012

def prefixReturnMachine : Machine 6 :=
  PSTRTMSeq005.seqMachine headerBackMachine PSTRTMMulRewind085.rewindMachine

def prefixReturnTrace (archive earlier : List Bool) (bit : Bool) (tail : List Bool) : List (MachineState 6) :=
  (headerBackTrace (PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive) false bit tail).map
      (PSTRTMSeq005.leftCfg (b:=3)) ++
    (PSTRTMPairRewind105.fullTrace archive earlier.reverse (bit::false::tail)).map
      (PSTRTMSeq005.rightCfg (a:=2))

def prefixReturnFinal (archive earlier : List Bool) (bit : Bool) (tail : List Bool) : MachineState 6 :=
  PSTRTMSeq005.rightCfg (a:=2)
    (PSTRTMMulRewind085.state 3 (false::archive) (PSTRTMIncrement009.blocks earlier++bit::false::tail))

theorem prefixReturn_runsFrom (archive earlier : List Bool) (bit : Bool) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom prefixReturnMachine
      ⟨0,Turing.Tape.mk₂ (false::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive)) tail⟩
      (prefixReturnTrace archive earlier bit tail) (prefixReturnFinal archive earlier bit tail) := by
  have h := PSTRTMSeq005.seq_runsFrom headerBackMachine PSTRTMMulRewind085.rewindMachine
    (headerState 0 (false::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive)) tail)
    (headerState 2 (PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive) (bit::false::tail))
    (PSTRTMMulRewind085.state 3 (false::archive) (PSTRTMIncrement009.blocks earlier++bit::false::tail))
    (headerBackTrace (PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive) false bit tail)
    (PSTRTMPairRewind105.fullTrace archive earlier.reverse (bit::false::tail))
    (headerBack_runsFrom (PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive) false bit tail)
    (PSTRTMPairRewind105.rewind_runsFrom archive earlier (bit::false::tail))
  simpa only [prefixReturnMachine,prefixReturnTrace,prefixReturnFinal,headerState,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem prefixReturnTrace_length (archive earlier : List Bool) (bit : Bool) (tail : List Bool) :
    (prefixReturnTrace archive earlier bit tail).length=2*earlier.length+6 := by
  change (((headerBackTrace (PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive) false bit tail).map
      (PSTRTMSeq005.leftCfg (a:=2) (b:=3))) ++
    (PSTRTMPairRewind105.fullTrace archive earlier.reverse (bit::false::tail)).map
      (PSTRTMSeq005.rightCfg (a:=2) (b:=3))).length = _
  rw [List.length_append,List.length_map,List.length_map,PSTRTMPairRewind105.full_length,List.length_reverse]
  change 3+(2*earlier.length+3) = _
  omega

def markedReturnMachine : Machine 12 := PSTRTMSeq005.seqMachine fieldBackMachine prefixReturnMachine

def markedArchive (archive earlier : List Bool) (bit : Bool) : List Bool :=
  bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive)

def markedReturnTrace (archive earlier later : List Bool) (bit : Bool) (suffix : List Bool) :
    List (MachineState 12) :=
  (fieldBackTrace (markedArchive archive earlier bit) later suffix).map
      (PSTRTMSeq005.leftCfg (b:=6)) ++
    (prefixReturnTrace archive earlier bit (PSTRTMIncrement009.blocks later++false::suffix)).map
      (PSTRTMSeq005.rightCfg (a:=5))

def markedReturnFinal (archive earlier later : List Bool) (bit : Bool) (suffix : List Bool) : MachineState 12 :=
  PSTRTMSeq005.rightCfg (a:=5)
    (prefixReturnFinal archive earlier bit (PSTRTMIncrement009.blocks later++false::suffix))

/-- The temporary flag is not an EOF shortcut. First rewind traverses the
real later data; LEFT2 crosses the cleared flag and its preceding data;
the second rewind reaches the original guard without altering either side. -/
theorem markedReturn_runsFrom (archive earlier later : List Bool) (bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom markedReturnMachine
      ⟨0,Turing.Tape.mk₂
        (false::(PSTRTMRawNat010.leftBlocks later.reverse++false::markedArchive archive earlier bit)) suffix⟩
      (markedReturnTrace archive earlier later bit suffix) (markedReturnFinal archive earlier later bit suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom fieldBackMachine prefixReturnMachine
    (⟨0,Turing.Tape.mk₂
      (false::(PSTRTMRawNat010.leftBlocks later.reverse++false::markedArchive archive earlier bit)) suffix⟩)
    (fieldBackFinal (markedArchive archive earlier bit) later suffix)
    (prefixReturnFinal archive earlier bit (PSTRTMIncrement009.blocks later++false::suffix))
    (fieldBackTrace (markedArchive archive earlier bit) later suffix)
    (prefixReturnTrace archive earlier bit (PSTRTMIncrement009.blocks later++false::suffix))
    (fieldBack_runsFrom (markedArchive archive earlier bit) later suffix)
    (prefixReturn_runsFrom archive earlier bit (PSTRTMIncrement009.blocks later++false::suffix))
  simpa only [markedReturnMachine,markedReturnTrace,markedReturnFinal,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem markedReturn_final_tape (archive earlier later : List Bool) (bit : Bool) (suffix : List Bool) :
    (markedReturnFinal archive earlier later bit suffix).Tape =
      Turing.Tape.mk₂ (false::archive)
        (PSTRTMIncrement009.blocks earlier++bit::false::(PSTRTMIncrement009.blocks later++false::suffix)) := rfl

theorem markedReturnTrace_length (archive earlier later : List Bool) (bit : Bool) (suffix : List Bool) :
    (markedReturnTrace archive earlier later bit suffix).length=2*(earlier.length+later.length)+11 := by
  change (((fieldBackTrace (markedArchive archive earlier bit) later suffix).map
      (PSTRTMSeq005.leftCfg (a:=5) (b:=6))) ++
    (prefixReturnTrace archive earlier bit (PSTRTMIncrement009.blocks later++false::suffix)).map
      (PSTRTMSeq005.rightCfg (a:=5) (b:=6))).length = _
  rw [List.length_append,List.length_map,List.length_map,fieldBackTrace_length,prefixReturnTrace_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
