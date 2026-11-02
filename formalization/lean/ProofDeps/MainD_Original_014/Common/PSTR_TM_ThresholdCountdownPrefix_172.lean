module
public import Common.PSTR_TM_ThresholdDepthEntry_171

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCountdownPrefix172
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthEntry171

private theorem depth_nonempty (depth : List Bool) (hp : true∈depth) : depth≠[] := by
  intro h
  simp only [h,List.not_mem_nil] at hp

def countMachine : Machine 14 := PSTRTMSeq005.seqMachine entryMachine PSTRTMThresholdCountdownCode164.countdownMachine

def countTrace (archive depth counter : List Bool) (gap : Nat) : List (MachineState 14) :=
  (entryTrace archive depth counter (gap+1)).map (PSTRTMSeq005.leftCfg (b:=8)) ++
    (PSTRTMThresholdCountdownRun166.borrowTrace archive 0 depth (retainedTail counter (gap+1))).map
      (PSTRTMSeq005.rightCfg (a:=5))

def countFinal (archive depth counter : List Bool) (gap : Nat) : MachineState 14 :=
  PSTRTMSeq005.rightCfg (a:=5) (PSTRTMThresholdCountdownCode164.state 8 (false::archive)
    (PSTRTMIncrement009.blocks (PSTRTMThresholdCountdownCode164.predDigits depth)++retainedTail counter (gap+1)))

theorem count_runsFrom (archive depth counter : List Bool) (gap : Nat) (hp : true∈depth) :
    PSTRTMSeq005.RunsFrom countMachine
      ⟨0,Turing.Tape.mk₂ (initialLeft archive depth (gap+1)) (PSTRTMIncrement009.blocks counter)⟩
      (countTrace archive depth counter gap) (countFinal archive depth counter gap) := by
  apply PSTRTMSeq005.seq_runsFrom entryMachine PSTRTMThresholdCountdownCode164.countdownMachine
    ⟨0,Turing.Tape.mk₂ (initialLeft archive depth (gap+1)) (PSTRTMIncrement009.blocks counter)⟩
    (entryFinal archive depth counter (gap+1))
    (PSTRTMThresholdCountdownCode164.state 8 (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMThresholdCountdownCode164.predDigits depth)++retainedTail counter (gap+1)))
    (entryTrace archive depth counter (gap+1))
    (PSTRTMThresholdCountdownRun166.borrowTrace archive 0 depth (retainedTail counter (gap+1)))
    (entry_runsFrom _ _ _ _ (depth_nonempty depth hp))
  rw [entry_final_tape]
  exact PSTRTMThresholdCountdownRun166.countdown_runsFrom _ _ _ hp

theorem count_final_tape (archive depth counter : List Bool) (gap : Nat) :
    (countFinal archive depth counter gap).Tape=Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMThresholdCountdownCode164.predDigits depth)++retainedTail counter (gap+1)) := rfl

/-- Fixed23 labels: actual B-to-depth seek/rewind, ONE binary borrow,
and the actual complete zero test. The last two halt labels retain the
observed result, ready for a real finite caller branch. No value, branch,
width, padding, fuel or runtime gap is an extra machine input. -/
def prefixMachine : Machine 22 := PSTRTMSeq005.seqMachine countMachine PSTRTMThresholdDepthZeroCode167.zeroMachine

def prefixTrace (archive depth counter : List Bool) (gap : Nat) : List (MachineState 22) :=
  (countTrace archive depth counter gap).map (PSTRTMSeq005.leftCfg (b:=7)) ++
    (PSTRTMThresholdDepthZeroRun168.zeroTrace archive [] false
      (PSTRTMThresholdCountdownCode164.predDigits depth) (retainedTail counter gap)).map
        (PSTRTMSeq005.rightCfg (a:=14))

def prefixFinal (archive depth counter : List Bool) (gap : Nat) : MachineState 22 :=
  PSTRTMSeq005.rightCfg (a:=14) (PSTRTMThresholdDepthZeroRun168.final archive [] false
    (PSTRTMThresholdCountdownCode164.predDigits depth) (retainedTail counter gap))

theorem prefix_runsFrom (archive depth counter : List Bool) (gap : Nat) (hp : true∈depth) :
    PSTRTMSeq005.RunsFrom prefixMachine
      ⟨0,Turing.Tape.mk₂ (initialLeft archive depth (gap+1)) (PSTRTMIncrement009.blocks counter)⟩
      (prefixTrace archive depth counter gap) (prefixFinal archive depth counter gap) := by
  apply PSTRTMSeq005.seq_runsFrom countMachine PSTRTMThresholdDepthZeroCode167.zeroMachine
    ⟨0,Turing.Tape.mk₂ (initialLeft archive depth (gap+1)) (PSTRTMIncrement009.blocks counter)⟩
    (countFinal archive depth counter gap)
    (PSTRTMThresholdDepthZeroRun168.final archive [] false
      (PSTRTMThresholdCountdownCode164.predDigits depth) (retainedTail counter gap))
    (countTrace archive depth counter gap)
    (PSTRTMThresholdDepthZeroRun168.zeroTrace archive [] false
      (PSTRTMThresholdCountdownCode164.predDigits depth) (retainedTail counter gap))
    (count_runsFrom _ _ _ _ hp)
  rw [count_final_tape]
  simpa only [PSTRTMThresholdDepthZeroRun168.inputRight,PSTRTMThresholdDepthZeroCode167.state,
    retainedTail,PSTRTMThresholdCounterSeek169.gaps,
    List.cons_append,List.append_assoc] using
    PSTRTMThresholdDepthZeroRun168.zero_runsFrom archive (PSTRTMThresholdCountdownCode164.predDigits depth)
      (retainedTail counter gap)

theorem prefix_final_tape (archive depth counter : List Bool) (gap : Nat) :
    (prefixFinal archive depth counter gap).Tape=Turing.Tape.mk₂
      (PSTRTMRawNat010.leftBlocks (PSTRTMThresholdCountdownCode164.predDigits depth).reverse++false::archive)
      (retainedTail counter (gap+1)) := by
  simp only [prefixFinal,PSTRTMSeq005.rightCfg,PSTRTMThresholdDepthZeroRun168.final,
    PSTRTMThresholdDepthZeroRun168.contextLeft,PSTRTMThresholdDepthZeroCode167.state,List.append_nil,
    retainedTail,PSTRTMThresholdCounterSeek169.gaps,List.cons_append]

/-- The return label is obtained from the read-only scan of the REAL
decremented word, even with leading zeros. This is not a supplied branch. -/
theorem prefix_final_label_zero_iff (archive depth counter : List Bool) (gap : Nat) (hp : true∈depth) :
    (prefixFinal archive depth counter gap).q.val=21 ↔ PSTRTMIncrement009.valueDigits depth=1 := by
  have hz := PSTRTMThresholdDepthZeroRun168.countdown_seen_false_iff depth hp
  change 15+(PSTRTMThresholdDepthZeroCode167.haltLabel
    (PSTRTMThresholdDepthZeroRun168.seen false (PSTRTMThresholdCountdownCode164.predDigits depth))).val=21 ↔ _
  cases hs : PSTRTMThresholdDepthZeroRun168.seen false (PSTRTMThresholdCountdownCode164.predDigits depth) <;>
    simpa [hs,PSTRTMThresholdDepthZeroCode167.haltLabel] using hz

theorem prefix_length_le (archive depth counter : List Bool) (gap : Nat) (hp : true∈depth) :
    (prefixTrace archive depth counter gap).length≤2*gap+9*depth.length+13 := by
  have he := entry_length archive depth counter (gap+1)
  have hc := PSTRTMThresholdCountdownRun166.borrow_length_le archive 0 depth (retainedTail counter (gap+1)) hp
  have hz := PSTRTMThresholdDepthZeroRun168.zero_length archive [] false
    (PSTRTMThresholdCountdownCode164.predDigits depth) (retainedTail counter gap)
  rw [PSTRTMThresholdCountdownCode164.pred_length] at hz
  simp only [prefixTrace,countTrace,List.length_append,List.length_map]
  omega

theorem prefix_visitedSpace_le (archive depth counter : List Bool) (gap : Nat) (hp : true∈depth) :
    visitedSpace prefixMachine (archive.length+1+2*depth.length+2*(gap+1)+2*counter.length)
      (prefixTrace archive depth counter gap)≤archive.length+2*counter.length+6*gap+20*depth.length+30 := by
  have ht := prefix_length_le archive depth counter gap hp
  have hs := PSTRTMTrace002.visitedSpace_le prefixMachine
    (archive.length+1+2*depth.length+2*(gap+1)+2*counter.length) (prefixTrace archive depth counter gap)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCountdownPrefix172
