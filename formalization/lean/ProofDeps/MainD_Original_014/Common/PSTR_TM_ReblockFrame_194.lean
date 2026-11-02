module
public import Common.PSTR_TM_PairRewind_105
public import Structure.PA17_TM_RatArithmetic_Parse_002c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMReblockFrame194
open PaperProofs.Common.Native.RationalControllerComputation

/-- Physically change the copy footer into the false guard needed by
the next parsed field. Every deeper archive cell is unchanged. -/
def guardMachine : Machine 3 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.write false)
  | 2 => some (3,.move .right)
  | _ => none

def guardTrace (left right : List Bool) : List (MachineState 3) :=
  [⟨0,Turing.Tape.mk₂ (true::left) right⟩,
   ⟨1,Turing.Tape.mk₂ left (true::right)⟩,
   ⟨2,Turing.Tape.mk₂ left (false::right)⟩,
   ⟨3,Turing.Tape.mk₂ (false::left) right⟩]

theorem guard_runsFrom (left right : List Bool) :
    PSTRTMSeq005.RunsFrom guardMachine ⟨0,Turing.Tape.mk₂ (true::left) right⟩
      (guardTrace left right) ⟨3,Turing.Tape.mk₂ (false::left) right⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [guardTrace,List.isChain_cons_cons,Turing.TM0.step,guardMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,guardMachine]

/-- The parser has REALLY reached the known final TRUE marker.
Erase that marker, then move onto the preceding real field-end FALSE.
This never scans01 as a flagged digit or assumes an arbitrary suffix blank. -/
def clearMachine : Machine 2 := fun q _ =>
  match q.val with
  | 0 => some (1,.write false)
  | 1 => some (2,.move .left)
  | _ => none

def clearTrace (left : List Bool) : List (MachineState 2) :=
  [⟨0,Turing.Tape.mk₂ (false::left) [true]⟩,
   ⟨1,Turing.Tape.mk₂ (false::left) [false]⟩,
   ⟨2,Turing.Tape.mk₂ left [false,false]⟩]

theorem clear_runsFrom (left : List Bool) :
    PSTRTMSeq005.RunsFrom clearMachine ⟨0,Turing.Tape.mk₂ (false::left) [true]⟩
      (clearTrace left) ⟨2,Turing.Tape.mk₂ left [false,false]⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [clearTrace,List.isChain_cons_cons,Turing.TM0.step,clearMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,clearMachine]

def clearRewindMachine : Machine 6 :=
  PSTRTMSeq005.seqMachine clearMachine PSTRTMMulRewind085.rewindMachine

def clearRewindTrace (left digits : List Bool) : List (MachineState 6) :=
  (clearTrace (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::left)).map
    (PSTRTMSeq005.leftCfg (b := 3)) ++
  (PSTRTMPairRewind105.fullTrace left digits.reverse [false,false]).map
    (PSTRTMSeq005.rightCfg (a := 2))

def clearRewindFinal (left digits : List Bool) : MachineState 6 :=
  PSTRTMSeq005.rightCfg (a := 2) (PSTRTMMulRewind085.state 3 (false::left)
    (PSTRTMIncrement009.blocks digits ++ [false,false]))

theorem clearRewind_runsFrom (left digits : List Bool) :
    PSTRTMSeq005.RunsFrom clearRewindMachine
      ⟨0,Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse ++ false::left)) [true]⟩
      (clearRewindTrace left digits) (clearRewindFinal left digits) := by
  apply PSTRTMSeq005.seq_runsFrom clearMachine PSTRTMMulRewind085.rewindMachine
    ⟨0,Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse ++ false::left)) [true]⟩
    ⟨2,Turing.Tape.mk₂ (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::left) [false,false]⟩
    (PSTRTMMulRewind085.state 3 (false::left) (PSTRTMIncrement009.blocks digits ++ [false,false]))
    (clearTrace (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::left))
    (PSTRTMPairRewind105.fullTrace left digits.reverse [false,false])
    (clear_runsFrom _) (PSTRTMPairRewind105.rewind_runsFrom _ _ _)

theorem clearRewind_length (left digits : List Bool) :
    (clearRewindTrace left digits).length = 2*digits.length + 6 := by
  simp only [clearRewindTrace,List.length_append,List.length_map,
    PSTRTMPairRewind105.full_length,List.length_reverse,clearTrace,List.length_cons,List.length_nil]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMReblockFrame194
