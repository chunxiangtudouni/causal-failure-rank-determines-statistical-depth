module
public import Common.PSTR_TM_ThresholdDepthSource_184

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthProgram185
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthSource184 PSTRTMThresholdDepthLoopTrace179

/-- One fixed1190-label program on the ORIGINAL risk/depth encoding.
Risk, depth, B, workspace and the answer never choose the program. This
computes the flagged B seed/recurrence, not the original FIVE Datum
threshold output; all other original localArithmetic domains stay open. -/
def depthMachine : Machine 1189 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdSeed155.seedMachine PSTRTMThresholdDepthLoopCode173.loopMachine

def depthTrace (risk : Rat) (depth : Nat) : List (MachineState 1189) :=
  (PSTRTMThresholdSeed155.seedTrace risk depth).map (PSTRTMSeq005.leftCfg (b:=387))++
    (loopTrace (riskArchive risk) (PSTRTMThresholdBackup139.depthDigits depth)
      (PaperProofs.Statistics.controllerB risk 1) (initialGap risk)).map (PSTRTMSeq005.rightCfg (a:=801))

def depthFinal (risk : Rat) (depth : Nat) : MachineState 1189 :=
  PSTRTMSeq005.rightCfg (a:=801) (loopFinal (riskArchive risk) (PSTRTMThresholdBackup139.depthDigits depth)
    (PaperProofs.Statistics.controllerB risk 1) (initialGap risk))

theorem depth_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1≤depth) :
    Runs depthMachine (encode [.rational risk,.natural depth]) (depthTrace risk depth) (depthFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs PSTRTMThresholdSeed155.seedMachine PSTRTMThresholdDepthLoopCode173.loopMachine
    (encode [.rational risk,.natural depth]) (PSTRTMThresholdSeed155.seedFinal risk depth)
    (loopFinal (riskArchive risk) (PSTRTMThresholdBackup139.depthDigits depth)
      (PaperProofs.Statistics.controllerB risk 1) (initialGap risk))
    (PSTRTMThresholdSeed155.seedTrace risk depth)
    (loopTrace (riskArchive risk) (PSTRTMThresholdBackup139.depthDigits depth)
      (PaperProofs.Statistics.controllerB risk 1) (initialGap risk))
    (PSTRTMThresholdSeed155.seed_runs risk depth hr)
  rw [seed_entry_tape risk depth hr]
  exact PSTRTMThresholdDepthLoopRun180.loop_runsFrom _ _ _ _ (depth_positive depth hd)

theorem depth_result_value (risk : Rat) (depth : Nat) (hd : 1≤depth) :
    (outcome (PSTRTMThresholdBackup139.depthDigits depth)
      (PaperProofs.Statistics.controllerB risk 1) (initialGap risk)).value=
        PaperProofs.Statistics.controllerB risk depth := by
  have h := (PSTRTMThresholdDepthLoopValue181.outcome_properties
    (PSTRTMThresholdBackup139.depthDigits depth) (PaperProofs.Statistics.controllerB risk 1)
    (initialGap risk) (depth_positive depth hd)).2.2
  rw [depth_value,PSTRTMThresholdDepthLoopValue181.advance_controllerB risk 1 (depth-1) (by decide)] at h
  have he : 1+(depth-1)=depth := by omega
  simpa only [he] using h

theorem depth_final_tape (risk : Rat) (depth : Nat) (hd : 1≤depth) :
    (depthFinal risk depth).Tape=Turing.Tape.mk₂
      (PSTRTMThresholdDepthEntry171.initialLeft (riskArchive risk)
        (outcome (PSTRTMThresholdBackup139.depthDigits depth)
          (PaperProofs.Statistics.controllerB risk 1) (initialGap risk)).depth
        ((outcome (PSTRTMThresholdBackup139.depthDigits depth)
          (PaperProofs.Statistics.controllerB risk 1) (initialGap risk)).gap+1))
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))) := by
  change (loopFinal _ _ _ _).Tape=_
  rw [PSTRTMThresholdDepthLoopRun180.loop_final_tape,depth_result_value risk depth hd]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthProgram185
