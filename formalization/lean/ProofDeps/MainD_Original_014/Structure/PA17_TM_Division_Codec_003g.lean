module
public import Structure.PA17_TM_Division_Codec_003f

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
open PaperProofs.Common.Native.RationalControllerComputation

def archiveContext (archive : List (Bool × Bool)) : List Bool :=
  false :: false :: false :: ((PSTRTMBinaryAdd024.operandColumns archive).reverse ++ [false])

def scanEraseMachine : Machine 26 :=
  PSTRTMSeq005.seqMachine PSTRTMCompareCode054.compareMachine eraseMachine

def scanEraseInitial (archive resident : List (Bool × Bool)) : MachineState 26 :=
  ⟨0, Turing.Tape.mk₂ (archiveContext archive)
    (PSTRTMBinaryAdd024.operandColumns resident ++ [false,false])⟩

def scanEraseTrace (archive resident : List (Bool × Bool)) : List (MachineState 26) :=
  (PSTRTMCompareTrace055.compareTrace 0 (archiveContext archive) [] resident []).map
      (PSTRTMSeq005.leftCfg (b := 5)) ++
    (eraseFullTrace
      (false :: false :: ((PSTRTMBinaryAdd024.operandColumns archive).reverse ++ [false]))
      (PSTRTMPackLoop043.pairedDigits resident) [false,false]).map
      (PSTRTMSeq005.rightCfg (a := 20))

def scanEraseFinal (archive : List (Bool × Bool)) : MachineState 26 :=
  PSTRTMSeq005.rightCfg (a := 20) (eraseState 5 (archiveContext archive) [])

private theorem blank_erased_own00 (count : Nat) :
    Turing.ListBlank.mk (List.replicate count false ++ [false,false]) =
      Turing.ListBlank.mk ([] : List Bool) := by
  change Turing.ListBlank.mk (List.replicate count false ++ List.replicate 2 false) = _
  rw [← List.replicate_add]
  simpa only [List.nil_append] using PSTRTMPackFinish039.blank_false_suffix [] (count + 2)

/-- The entire resident region is actually visited, erased flag by flag
and data by data, and then represented by genuine blank tape. The archive
and all three separator cells have not been discarded or reloaded. -/
theorem scanErase_runsFrom (archive resident : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom scanEraseMachine (scanEraseInitial archive resident)
      (scanEraseTrace archive resident) (scanEraseFinal archive) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMCompareCode054.compareMachine eraseMachine
    _ _ _ _ _ (PSTRTMCompareTrace055.compare_runsFrom 0 (archiveContext archive) resident [])
  change PSTRTMSeq005.RunsFrom eraseMachine
    (eraseState 0 (PSTRTMCompareCode054.leftColumns resident.reverse ++ archiveContext archive)
      [false,false]) _ (eraseState 5 (archiveContext archive) [])
  rw [PSTRTMCompareRun059.leftColumns_reverse]
  have hr := erase_runsFrom
    (false :: false :: ((PSTRTMBinaryAdd024.operandColumns archive).reverse ++ [false]))
    (PSTRTMPackLoop043.pairedDigits resident) [false,false]
  have hf : eraseState 5 (archiveContext archive)
      (List.replicate (2 * (PSTRTMPackLoop043.pairedDigits resident).length) false ++ [false,false]) =
      eraseState 5 (archiveContext archive) [] := by
    simp only [eraseState, Turing.Tape.mk₂]
    rw [blank_erased_own00]
  dsimp only [archiveContext] at hf
  rw [hf] at hr
  exact hr

theorem scanEraseTrace_length (archive resident : List (Bool × Bool)) :
    (scanEraseTrace archive resident).length = 12 * resident.length + 6 := by
  simp only [scanEraseTrace, List.length_append, List.length_map,
    PSTRTMCompareTrace055.compare_length, eraseFullTrace_length,
    PSTRTMCompareRun059.pairedDigits_length]
  omega

def quotientProjectMachine : Machine 36 :=
  PSTRTMSeq005.seqMachine scanEraseMachine returnArchiveMachine

def quotientProjectTrace (archive resident : List (Bool × Bool)) : List (MachineState 36) :=
  (scanEraseTrace archive resident).map (PSTRTMSeq005.leftCfg (b := 9)) ++
    (returnArchiveTrace archive []).map (PSTRTMSeq005.rightCfg (a := 26))

def quotientProjectFinal (archive : List (Bool × Bool)) : MachineState 36 :=
  PSTRTMSeq005.rightCfg (a := 26) (returnArchiveFinal archive [])

theorem quotientProject_runsFrom (archive resident : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom quotientProjectMachine
      (PSTRTMSeq005.leftCfg (b := 9) (scanEraseInitial archive resident))
      (quotientProjectTrace archive resident) (quotientProjectFinal archive) := by
  apply PSTRTMSeq005.seq_runsFrom scanEraseMachine returnArchiveMachine
    _ _ _ _ _ (scanErase_runsFrom archive resident)
  have hr := returnArchive_runsFrom archive []
  unfold returnArchiveInitial at hr
  rw [leftColumns_reverse_columns] at hr
  exact hr

theorem quotientProject_final_tape (archive : List (Bool × Bool)) :
    (quotientProjectFinal archive).Tape = Turing.Tape.mk₁ (PSTRTMBinaryAdd024.operandColumns archive) :=
  returnArchive_final_tape archive

def isolatedOutputMachine : Machine 103 :=
  PSTRTMSeq005.seqMachine projectAMachine resultCodecMachine

def isolatedOutputTrace (pairs : List (Bool × Bool)) : List (MachineState 103) :=
  (projectATrace [] pairs []).map (PSTRTMSeq005.leftCfg (b := 91)) ++
    (resultCodecTrace (firstBits pairs)).map (PSTRTMSeq005.rightCfg (a := 11))

def isolatedOutputFinal (pairs : List (Bool × Bool)) : MachineState 103 :=
  PSTRTMSeq005.rightCfg (a := 11) (resultCodecFinal (firstBits pairs))

theorem isolatedOutput_runsFrom (pairs : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom isolatedOutputMachine
      ⟨0, Turing.Tape.mk₁ (PSTRTMBinaryAdd024.operandColumns pairs)⟩
      (isolatedOutputTrace pairs) (isolatedOutputFinal pairs) := by
  apply PSTRTMSeq005.seq_runsFrom projectAMachine resultCodecMachine
    _ _ _ _ _ (projectA_isolated_runsFrom pairs)
  rw [projectA_final_tape]
  have hr := resultCodec_runs (firstBits pairs)
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

theorem isolatedOutput_final_tape (pairs : List (Bool × Bool)) :
    (isolatedOutputFinal pairs).Tape = Turing.Tape.mk₁ (encodeNat (PSTRTMBinaryAdd024.firstValue pairs)) := by
  have hr := resultCodec_final_tape (firstBits pairs)
  rw [firstBits_value] at hr
  exact hr

/-- Fixed141-label quotient postlude. It really clears the resident tail,
crosses the actual separator, rewinds the archive and executes projection,
compaction, canonical trimming and inverse encoding. No pending-track
correctness assumption is required to read the actual first archive track. -/
def quotientTailMachine : Machine 140 :=
  PSTRTMSeq005.seqMachine quotientProjectMachine isolatedOutputMachine

def quotientTailInitial (archive resident : List (Bool × Bool)) : MachineState 140 :=
  ⟨0, (scanEraseInitial archive resident).Tape⟩

def quotientTailTrace (archive resident : List (Bool × Bool)) : List (MachineState 140) :=
  (quotientProjectTrace archive resident).map (PSTRTMSeq005.leftCfg (b := 103)) ++
    (isolatedOutputTrace archive).map (PSTRTMSeq005.rightCfg (a := 36))

def quotientTailFinal (archive : List (Bool × Bool)) : MachineState 140 :=
  PSTRTMSeq005.rightCfg (a := 36) (isolatedOutputFinal archive)

theorem quotientTail_runsFrom (archive resident : List (Bool × Bool)) :
    PSTRTMSeq005.RunsFrom quotientTailMachine (quotientTailInitial archive resident)
      (quotientTailTrace archive resident) (quotientTailFinal archive) := by
  apply PSTRTMSeq005.seq_runsFrom quotientProjectMachine isolatedOutputMachine
    _ _ _ _ _ (quotientProject_runsFrom archive resident)
  rw [quotientProject_final_tape]
  exact isolatedOutput_runsFrom archive

theorem quotientTail_final_tape (archive : List (Bool × Bool)) :
    (quotientTailFinal archive).Tape = Turing.Tape.mk₁ (encodeNat (PSTRTMBinaryAdd024.firstValue archive)) :=
  isolatedOutput_final_tape archive

theorem quotientTailTrace_length_le (archive resident : List (Bool × Bool)) :
    (quotientTailTrace archive resident).length ≤
      12 * resident.length + 13 * archive.length + 19 + 128 * (archive.length + 1)^2 := by
  have hc := resultCodecTrace_length_le (firstBits archive)
  rw [firstBits_length] at hc
  simp only [quotientTailTrace, quotientProjectTrace, isolatedOutputTrace,
    List.length_append, List.length_map, scanEraseTrace_length, returnArchiveTrace_length,
    projectATrace_length]
  omega

theorem quotientTailTrace_visitedSpace_le (inputLength : Nat) (archive resident : List (Bool × Bool)) :
    visitedSpace quotientTailMachine inputLength (quotientTailTrace archive resident) ≤
      inputLength + 24 * resident.length + 26 * archive.length + 39 + 256 * (archive.length + 1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le quotientTailMachine inputLength (quotientTailTrace archive resident)
  have ht := quotientTailTrace_length_le archive resident
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
