module
public import Common.PSTR_TM_ThresholdDepthLoopLift_174

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCounterReturn175
open PaperProofs.Common.Native.RationalControllerComputation

def counterHead (value : Nat) : Bool := (PSTRTMNatValue017.rawPayload value).headD false
def counterTail (value : Nat) : List Bool := (PSTRTMNatValue017.rawPayload value).tail

theorem counter_blocks (value : Nat) :
    PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value)=
      counterHead value::true::PSTRTMIncrement009.blocks (counterTail value) := by
  have hn := PSTRTMThresholdUnitColumnsCost160.rawPayload_ne_nil value
  cases he : PSTRTMNatValue017.rawPayload value with
  | nil => exact False.elim (hn he)
  | cons bit later => simp only [counterHead,counterTail,he,List.headD_cons,List.tail_cons,
      PSTRTMIncrement009.blocks,List.flatMap_cons,List.cons_append,List.nil_append]

def returnLeft (archive depth : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks (PSTRTMThresholdCountdownCode164.predDigits depth).reverse++false::archive

def returnTrace (archive depth : List Bool) (value gap : Nat) : List (MachineState 2) :=
  PSTRTMThresholdCounterSeek169.seekTrace (counterHead value) (PSTRTMIncrement009.blocks (counterTail value))
    (gap+1) (returnLeft archive depth)

def returnFinal (archive depth : List Bool) (value gap : Nat) : MachineState 2 :=
  PSTRTMThresholdCounterSeek169.state 2
    (PSTRTMThresholdCounterSeek169.gapLeft (gap+1) (returnLeft archive depth))
    (counterHead value::true::PSTRTMIncrement009.blocks (counterTail value))

/-- Real zero/positive-mode return subroutine from the depth prefix's
actual EOF position. It reads every00 gap pair and the true B flag,
then returns one cell left. Canonical B0 is supported too; source B's
LSB is never mistaken for a blank end. No head reset or copy occurs. -/
theorem return_runsFrom (archive depth : List Bool) (value gap : Nat) :
    PSTRTMSeq005.RunsFrom PSTRTMThresholdCounterSeek169.seekMachine
      ⟨0,(PSTRTMThresholdCountdownPrefix172.prefixFinal archive depth (PSTRTMNatValue017.rawPayload value) gap).Tape⟩
      (returnTrace archive depth value gap) (returnFinal archive depth value gap) := by
  rw [PSTRTMThresholdCountdownPrefix172.prefix_final_tape]
  simp only [PSTRTMThresholdDepthEntry171.retainedTail,counter_blocks]
  exact PSTRTMThresholdCounterSeek169.seek_runsFrom _ _ _ _

theorem return_final_tape (archive depth : List Bool) (value gap : Nat) :
    (returnFinal archive depth value gap).Tape=Turing.Tape.mk₂
      (PSTRTMThresholdDepthEntry171.initialLeft archive (PSTRTMThresholdCountdownCode164.predDigits depth) (gap+1))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value)) := by
  simp only [returnFinal,PSTRTMThresholdCounterSeek169.state,PSTRTMThresholdCounterSeek169.gapLeft_eq,
    returnLeft,PSTRTMThresholdDepthEntry171.initialLeft,counter_blocks]

theorem return_length (archive depth : List Bool) (value gap : Nat) :
    (returnTrace archive depth value gap).length=2*gap+5 := by
  simp only [returnTrace,PSTRTMThresholdCounterSeek169.seek_length]
  omega

theorem return_visitedSpace_le (archive depth : List Bool) (value gap : Nat) :
    visitedSpace PSTRTMThresholdCounterSeek169.seekMachine
      (archive.length+1+2*depth.length+2*(gap+1)+2*natBits value) (returnTrace archive depth value gap)≤
      archive.length+2*natBits value+2*depth.length+6*gap+14 := by
  have h := PSTRTMTrace002.visitedSpace_le PSTRTMThresholdCounterSeek169.seekMachine
    (archive.length+1+2*depth.length+2*(gap+1)+2*natBits value) (returnTrace archive depth value gap)
  rw [return_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCounterReturn175
