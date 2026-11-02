module
public import Structure.PA17_TM_Division_Codec_003d

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
open PaperProofs.Common.Native.RationalControllerComputation

def firstBits (pairs : List (Bool × Bool)) : List Bool := pairs.map Prod.fst

theorem firstBits_length (pairs : List (Bool × Bool)) : (firstBits pairs).length = pairs.length := by
  simp only [firstBits, List.length_map]

theorem firstBits_value (pairs : List (Bool × Bool)) :
    PSTRTMIncrement009.valueDigits (firstBits pairs) = PSTRTMBinaryAdd024.firstValue pairs := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
      obtain ⟨a,b⟩ := pair
      change Nat.bit a (PSTRTMIncrement009.valueDigits (firstBits later)) =
        Nat.bit a (PSTRTMBinaryAdd024.firstValue later)
      rw [ih]

theorem clearBPairs_columns (pairs : List (Bool × Bool)) :
    PSTRTMBinaryAdd024.operandColumns (clearBPairs pairs) =
      PSTRTMBinaryAdd024.resultColumns (firstBits pairs) := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
      obtain ⟨a,b⟩ := pair
      change (a :: true :: false :: true :: PSTRTMBinaryAdd024.operandColumns (clearBPairs later)) =
        (a :: true :: false :: true :: PSTRTMBinaryAdd024.resultColumns (firstBits later))
      rw [ih]

private theorem blank_own00 (word : List Bool) :
    Turing.ListBlank.mk (word ++ [false,false]) = Turing.ListBlank.mk word := by
  exact PSTRTMPackFinish039.blank_false_suffix word 2

def projectAFinal (pairs : List (Bool × Bool)) : MachineState 11 :=
  PSTRTMSeq005.rightCfg (a := 5)
    (PSTRTMColumnRewind067.state 5 [false]
      (PSTRTMBinaryAdd024.operandColumns (clearBPairs pairs) ++ [false,false]))

theorem projectA_isolated_runsFrom (pairs : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom projectAMachine
      ⟨0, Turing.Tape.mk₁ (PSTRTMBinaryAdd024.operandColumns pairs)⟩
      (projectATrace [] pairs []) (projectAFinal pairs) := by
  have hr := projectA_runsFrom [] pairs []
  have hi : PSTRTMSeq005.leftCfg (b := 5)
      (clearBState 0 [false] (PSTRTMBinaryAdd024.operandColumns pairs ++ [false,false])) =
      (⟨0, Turing.Tape.mk₁ (PSTRTMBinaryAdd024.operandColumns pairs)⟩ : MachineState 11) := by
    simp only [PSTRTMSeq005.leftCfg, PSTRTMSeq005.leftLabel, clearBState,
      Turing.Tape.mk₁, Turing.Tape.mk₂]
    rw [PSTRTMRawNat010.blank_single_false, blank_own00]
    rfl
  rw [hi] at hr
  exact hr

theorem projectA_final_tape (pairs : List (Bool × Bool)) :
    (projectAFinal pairs).Tape =
      Turing.Tape.mk₁ (PSTRTMBinaryAdd024.resultColumns (firstBits pairs)) := by
  simp only [projectAFinal, PSTRTMSeq005.rightCfg, PSTRTMColumnRewind067.state,
    Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false, blank_own00, clearBPairs_columns]

def remainderProjectMachine : Machine 25 :=
  PSTRTMSeq005.seqMachine dropArchiveMachine projectAMachine

/-- The fixed118-label remainder postlude erases the archive, physically
projects and rewinds the resident result, then runs all three real codecs. -/
def remainderTailMachine : Machine 117 :=
  PSTRTMSeq005.seqMachine remainderProjectMachine resultCodecMachine

def remainderProjectInitial (archiveDigits : List Bool) (pairs : List (Bool × Bool)) : MachineState 25 :=
  ⟨0, Turing.Tape.mk₂
    (false :: false :: false :: (PSTRTMRawNat010.leftBlocks archiveDigits.reverse ++ [false]))
    (PSTRTMBinaryAdd024.operandColumns pairs)⟩

def remainderProjectTrace (archiveDigits : List Bool) (pairs : List (Bool × Bool)) : List (MachineState 25) :=
  (dropArchiveTrace archiveDigits (PSTRTMBinaryAdd024.operandColumns pairs)).map
      (PSTRTMSeq005.leftCfg (b := 11)) ++
    (projectATrace [] pairs []).map (PSTRTMSeq005.rightCfg (a := 13))

def remainderProjectFinal (pairs : List (Bool × Bool)) : MachineState 25 :=
  PSTRTMSeq005.rightCfg (a := 13) (projectAFinal pairs)

def remainderTailInitial (archiveDigits : List Bool) (pairs : List (Bool × Bool)) : MachineState 117 :=
  ⟨0, (remainderProjectInitial archiveDigits pairs).Tape⟩

def remainderTailTrace (archiveDigits : List Bool) (pairs : List (Bool × Bool)) : List (MachineState 117) :=
  (remainderProjectTrace archiveDigits pairs).map (PSTRTMSeq005.leftCfg (b := 91)) ++
    (resultCodecTrace (firstBits pairs)).map (PSTRTMSeq005.rightCfg (a := 25))

def remainderTailFinal (pairs : List (Bool × Bool)) : MachineState 117 :=
  PSTRTMSeq005.rightCfg (a := 25) (resultCodecFinal (firstBits pairs))

theorem remainderProject_runsFrom (archiveDigits : List Bool) (pairs : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom remainderProjectMachine (remainderProjectInitial archiveDigits pairs)
      (remainderProjectTrace archiveDigits pairs) (remainderProjectFinal pairs) := by
  apply PSTRTMSeq005.seq_runsFrom dropArchiveMachine projectAMachine
    _ _ _ _ _ (dropArchive_runsFrom archiveDigits (PSTRTMBinaryAdd024.operandColumns pairs))
  rw [dropArchive_final_tape]
  exact projectA_isolated_runsFrom pairs

theorem remainderProject_final_tape (pairs : List (Bool × Bool)) :
    (remainderProjectFinal pairs).Tape =
      Turing.Tape.mk₁ (PSTRTMBinaryAdd024.resultColumns (firstBits pairs)) :=
  projectA_final_tape pairs

theorem remainderTail_runsFrom (archiveDigits : List Bool) (pairs : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom remainderTailMachine (remainderTailInitial archiveDigits pairs)
      (remainderTailTrace archiveDigits pairs) (remainderTailFinal pairs) := by
  apply PSTRTMSeq005.seq_runsFrom remainderProjectMachine resultCodecMachine
    _ _ _ _ _ (remainderProject_runsFrom archiveDigits pairs)
  rw [remainderProject_final_tape]
  have hr := resultCodec_runs (firstBits pairs)
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem remainderTail_final_tape (pairs : List (Bool × Bool)) :
    (remainderTailFinal pairs).Tape = Turing.Tape.mk₁ (encodeNat (PSTRTMBinaryAdd024.firstValue pairs)) := by
  have hr := resultCodec_final_tape (firstBits pairs)
  rw [firstBits_value] at hr
  exact hr

theorem remainderTailTrace_length_le (archiveDigits : List Bool) (pairs : List (Bool × Bool)) :
    (remainderTailTrace archiveDigits pairs).length ≤
      6 * archiveDigits.length + 9 * pairs.length + 19 + 128 * (pairs.length + 1)^2 := by
  have hc := resultCodecTrace_length_le (firstBits pairs)
  rw [firstBits_length] at hc
  simp only [remainderTailTrace, remainderProjectTrace, List.length_append, List.length_map,
    dropArchiveTrace_length, projectATrace_length]
  omega

theorem remainderTailTrace_visitedSpace_le (inputLength : Nat) (archiveDigits : List Bool)
    (pairs : List (Bool × Bool)) :
    visitedSpace remainderTailMachine inputLength (remainderTailTrace archiveDigits pairs) ≤
      inputLength + 12 * archiveDigits.length + 18 * pairs.length + 39 + 256 * (pairs.length + 1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le remainderTailMachine inputLength (remainderTailTrace archiveDigits pairs)
  have ht := remainderTailTrace_length_le archiveDigits pairs
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
