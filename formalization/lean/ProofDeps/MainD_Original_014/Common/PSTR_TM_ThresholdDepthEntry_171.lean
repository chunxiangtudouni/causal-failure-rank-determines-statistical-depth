module
public import Common.PSTR_TM_ThresholdDepthSeek_163
public import Common.PSTR_TM_ThresholdCounterSeek_169
public import Common.PSTR_TM_ThresholdDepthRewind_170

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthEntry171
open PaperProofs.Common.Native.RationalControllerComputation

def highLeft (archive depth : List Bool) : List Bool :=
  match depth.reverse with
  | [] => archive
  | bit::earlier => bit::(PSTRTMRawNat010.leftBlocks earlier++false::archive)

def initialLeft (archive depth : List Bool) (gap : Nat) : List Bool :=
  PSTRTMThresholdCounterSeek169.gaps gap++(PSTRTMRawNat010.leftBlocks depth.reverse++false::archive)

def retainedTail (counter : List Bool) (gap : Nat) : List Bool :=
  PSTRTMThresholdCounterSeek169.gaps gap++PSTRTMIncrement009.blocks counter

private theorem reverse_nonempty (depth : List Bool) (hn : depth≠[]) : depth.reverse≠[] := by
  intro h
  have hr := congrArg List.reverse h
  simp only [List.reverse_reverse,List.reverse_nil] at hr
  exact hn hr

theorem initial_left (archive depth : List Bool) (gap : Nat) (hn : depth≠[]) :
    initialLeft archive depth gap=List.replicate (2*gap) false++true::highLeft archive depth := by
  have hp := reverse_nonempty depth hn
  cases he : depth.reverse with
  | nil => exact False.elim (hp he)
  | cons bit earlier =>
    simp only [initialLeft,highLeft,he,PSTRTMThresholdCounterSeek169.gaps_replicate,
      PSTRTMRawNat010.leftBlocks,List.flatMap_cons,List.cons_append,List.nil_append]

def firstFinal (archive depth counter : List Bool) (gap : Nat) : MachineState 2 :=
  PSTRTMThresholdDepthSeek163.state 2 (highLeft archive depth)
    (true::(List.replicate (2*gap) false++PSTRTMIncrement009.blocks counter))

private theorem rewind_initial_zero (archive depth tail : List Bool) :
    PSTRTMThresholdDepthRewind170.initial archive depth tail=
      (⟨0,(PSTRTMThresholdDepthRewind170.initial archive depth tail).Tape⟩ : MachineState 2) := by
  calc
    PSTRTMThresholdDepthRewind170.initial archive depth tail=
        (⟨(PSTRTMThresholdDepthRewind170.initial archive depth tail).q,
          (PSTRTMThresholdDepthRewind170.initial archive depth tail).Tape⟩ : MachineState 2) := rfl
    _=⟨0,(PSTRTMThresholdDepthRewind170.initial archive depth tail).Tape⟩ := by
      rw [PSTRTMThresholdDepthRewind170.initial_label]

theorem flag_boundary (archive depth counter : List Bool) (gap : Nat) (hn : depth≠[]) :
    (⟨0,(firstFinal archive depth counter gap).Tape⟩ : MachineState 2)=
      PSTRTMThresholdDepthRewind170.initial archive depth (retainedTail counter gap) := by
  rw [rewind_initial_zero]
  congr 1
  have hp := reverse_nonempty depth hn
  cases he : depth.reverse with
  | nil => exact False.elim (hp he)
  | cons bit earlier =>
    simp only [firstFinal,highLeft,he,retainedTail,PSTRTMThresholdCounterSeek169.gaps_replicate,
      PSTRTMThresholdDepthSeek163.state,PSTRTMThresholdDepthRewind170.initial,
      PSTRTMThresholdDepthRewind170.lowerCfg,PSTRTMPairRewind105.initial,PSTRTMMulRewind085.state]

/-- Fixed six-label B-to-DEPTH entry. The head really traverses the
entire cleared gap, reads the actual last depth flag, and rewinds every
source pair. Both the original risk archive and entire B word survive. -/
def entryMachine : Machine 5 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdDepthSeek163.seekMachine PSTRTMThresholdDepthRewind170.rewindMachine

def entryTrace (archive depth counter : List Bool) (gap : Nat) : List (MachineState 5) :=
  (PSTRTMThresholdDepthSeek163.seekTrace (highLeft archive depth) (PSTRTMIncrement009.blocks counter) (2*gap)).map
    (PSTRTMSeq005.leftCfg (b:=2)) ++
  (PSTRTMThresholdDepthRewind170.rewindTrace archive depth (retainedTail counter gap)).map
    (PSTRTMSeq005.rightCfg (a:=2))

def entryFinal (archive depth counter : List Bool) (gap : Nat) : MachineState 5 :=
  PSTRTMSeq005.rightCfg (a:=2) (PSTRTMThresholdDepthRewind170.state 2 (false::archive)
    (PSTRTMIncrement009.blocks depth++retainedTail counter gap))

theorem entry_runsFrom (archive depth counter : List Bool) (gap : Nat) (hn : depth≠[]) :
    PSTRTMSeq005.RunsFrom entryMachine
      ⟨0,Turing.Tape.mk₂ (initialLeft archive depth gap) (PSTRTMIncrement009.blocks counter)⟩
      (entryTrace archive depth counter gap) (entryFinal archive depth counter gap) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMThresholdDepthSeek163.seekMachine PSTRTMThresholdDepthRewind170.rewindMachine
    (PSTRTMThresholdDepthSeek163.state 0 (initialLeft archive depth gap) (PSTRTMIncrement009.blocks counter))
    (firstFinal archive depth counter gap)
    (PSTRTMThresholdDepthRewind170.state 2 (false::archive) (PSTRTMIncrement009.blocks depth++retainedTail counter gap))
    (PSTRTMThresholdDepthSeek163.seekTrace (highLeft archive depth) (PSTRTMIncrement009.blocks counter) (2*gap))
    (PSTRTMThresholdDepthRewind170.rewindTrace archive depth (retainedTail counter gap))
  · rw [initial_left archive depth gap hn]
    exact PSTRTMThresholdDepthSeek163.seek_runsFrom _ _ _
  · rw [flag_boundary archive depth counter gap hn]
    exact PSTRTMThresholdDepthRewind170.rewind_runsFrom _ _ _

theorem entry_final_tape (archive depth counter : List Bool) (gap : Nat) :
    (entryFinal archive depth counter gap).Tape=Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks depth++retainedTail counter gap) := rfl

theorem entry_length (archive depth counter : List Bool) (gap : Nat) :
    (entryTrace archive depth counter gap).length=2*gap+2*depth.length+5 := by
  simp only [entryTrace,List.length_append,List.length_map,PSTRTMThresholdDepthSeek163.seek_length,
    PSTRTMThresholdDepthRewind170.rewind_length]
  omega

theorem entry_visitedSpace_le (archive depth counter : List Bool) (gap : Nat) :
    visitedSpace entryMachine (archive.length+1+2*depth.length+2*gap+2*counter.length)
      (entryTrace archive depth counter gap)≤archive.length+2*counter.length+6*gap+6*depth.length+12 := by
  have h := PSTRTMTrace002.visitedSpace_le entryMachine
    (archive.length+1+2*depth.length+2*gap+2*counter.length) (entryTrace archive depth counter gap)
  rw [entry_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthEntry171
