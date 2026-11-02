module
public import Common.PSTR_TM_ThresholdBackupReturn_227
public import Common.PSTR_TM_ThresholdDepthSeek_163

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRiskReturn228
open PaperProofs.Common.Native.RationalControllerComputation

/-! Actual return across the retained cleared gap to an archived flagged
field. The actual source TRUE flag is found by163, not by a supplied width.
One real right move restores its EOF position, then SAME105 rewinds it.
Arbitrary archive and the complete right suffix are retained literally.
The direct consumer is the exhausted DEPTH field between saved B and risk. -/

def rightMachine : Machine 1 := fun q _ =>
  if q.val = 0 then some (1,.move .right) else none

def rightTrace (left right : List Bool) : List (MachineState 1) :=
  [⟨0,Turing.Tape.mk₂ left (true::right)⟩,⟨1,Turing.Tape.mk₂ (true::left) right⟩]

theorem right_runsFrom (left right : List Bool) :
    PSTRTMSeq005.RunsFrom rightMachine ⟨0,Turing.Tape.mk₂ left (true::right)⟩
      (rightTrace left right) ⟨1,Turing.Tape.mk₂ (true::left) right⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [rightTrace,List.isChain_cons_cons,Turing.TM0.step,rightMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,rightMachine]

def seekReturnMachine : Machine 4 :=
  PSTRTMSeq005.seqMachine PSTRTMThresholdDepthSeek163.seekMachine rightMachine

def seekReturnTrace (left right : List Bool) (gap : Nat) : List (MachineState 4) :=
  (PSTRTMThresholdDepthSeek163.seekTrace left right gap).map (PSTRTMSeq005.leftCfg (b := 1)) ++
    (rightTrace left (List.replicate gap false++right)).map (PSTRTMSeq005.rightCfg (a := 2))

def seekReturnFinal (left right : List Bool) (gap : Nat) : MachineState 4 :=
  PSTRTMSeq005.rightCfg (a := 2) (b := 1)
    ⟨1,Turing.Tape.mk₂ (true::left) (List.replicate gap false++right)⟩

theorem seekReturn_runsFrom (left right : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom seekReturnMachine
      ⟨0,Turing.Tape.mk₂ (List.replicate gap false++true::left) right⟩
      (seekReturnTrace left right gap) (seekReturnFinal left right gap) := by
  apply PSTRTMSeq005.seq_runsFrom PSTRTMThresholdDepthSeek163.seekMachine rightMachine
    (PSTRTMThresholdDepthSeek163.state 0 (List.replicate gap false++true::left) right)
    (PSTRTMThresholdDepthSeek163.state 2 left (true::(List.replicate gap false++right)))
    ⟨1,Turing.Tape.mk₂ (true::left) (List.replicate gap false++right)⟩
    (PSTRTMThresholdDepthSeek163.seekTrace left right gap)
    (rightTrace left (List.replicate gap false++right))
    (PSTRTMThresholdDepthSeek163.seek_runsFrom _ _ _)
  exact right_runsFrom _ _

def depthMachine : Machine 8 :=
  PSTRTMSeq005.seqMachine seekReturnMachine PSTRTMMulRewind085.rewindMachine

def depthTrace (archive : List Bool) (bit : Bool) (earlier right : List Bool) (gap : Nat) :
    List (MachineState 8) :=
  (seekReturnTrace (bit::(PSTRTMRawNat010.leftBlocks earlier++false::archive)) right gap).map
    (PSTRTMSeq005.leftCfg (b := 3)) ++
    (PSTRTMPairRewind105.fullTrace archive (bit::earlier) (List.replicate gap false++right)).map
      (PSTRTMSeq005.rightCfg (a := 4))

def depthFinal (archive : List Bool) (bit : Bool) (earlier right : List Bool) (gap : Nat) :
    MachineState 8 :=
  PSTRTMSeq005.rightCfg (a := 4) (PSTRTMMulRewind085.state 3 (false::archive)
    (PSTRTMIncrement009.blocks (bit::earlier).reverse++List.replicate gap false++right))

theorem depth_runsFrom (archive : List Bool) (bit : Bool) (earlier right : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom depthMachine
      ⟨0,Turing.Tape.mk₂
        (List.replicate gap false++(PSTRTMRawNat010.leftBlocks (bit::earlier)++false::archive)) right⟩
      (depthTrace archive bit earlier right gap) (depthFinal archive bit earlier right gap) := by
  apply PSTRTMSeq005.seq_runsFrom seekReturnMachine PSTRTMMulRewind085.rewindMachine
    ⟨0,Turing.Tape.mk₂
      (List.replicate gap false++(PSTRTMRawNat010.leftBlocks (bit::earlier)++false::archive)) right⟩
    (seekReturnFinal (bit::(PSTRTMRawNat010.leftBlocks earlier++false::archive)) right gap)
    (PSTRTMMulRewind085.state 3 (false::archive)
      (PSTRTMIncrement009.blocks (bit::earlier).reverse++List.replicate gap false++right))
    (seekReturnTrace (bit::(PSTRTMRawNat010.leftBlocks earlier++false::archive)) right gap)
    (PSTRTMPairRewind105.fullTrace archive (bit::earlier) (List.replicate gap false++right))
  · exact seekReturn_runsFrom _ _ _
  · refine ⟨PSTRTMPairRewind105.full_head _ _ _,PSTRTMPairRewind105.full_chain _ _ _,?_,
      PSTRTMPairRewind105.rewind_halt _ _⟩
    simpa only [List.append_assoc] using
      PSTRTMPairRewind105.full_last archive (bit::earlier) (List.replicate gap false++right)

theorem depth_final_tape (archive : List Bool) (bit : Bool) (earlier right : List Bool) (gap : Nat) :
    (depthFinal archive bit earlier right gap).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks (bit::earlier).reverse++List.replicate gap false++right) := rfl

theorem depth_length (archive : List Bool) (bit : Bool) (earlier right : List Bool) (gap : Nat) :
    (depthTrace archive bit earlier right gap).length = gap+2*earlier.length+10 := by
  simp only [depthTrace,seekReturnTrace,List.length_append,List.length_map,
    PSTRTMThresholdDepthSeek163.seek_length,rightTrace,List.length_cons,List.length_nil,
    PSTRTMPairRewind105.full_length]
  omega

theorem depth_prefix_space_le (archive : List Bool) (bit : Bool) (earlier right : List Bool)
    (gap input clock : Nat) :
    visitedSpace depthMachine input ((depthTrace archive bit earlier right gap).take clock) ≤
      input+2*gap+4*earlier.length+21 := by
  have hs := PSTRTMTrace002.visitedSpace_le depthMachine input
    ((depthTrace archive bit earlier right gap).take clock)
  have hl : ((depthTrace archive bit earlier right gap).take clock).length ≤
      (depthTrace archive bit earlier right gap).length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  rw [depth_length] at hl
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdRiskReturn228
