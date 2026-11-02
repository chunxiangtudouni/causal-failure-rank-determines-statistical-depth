module
public import Common.PSTR_TM_ThresholdDepthCost_186
public import Common.PSTR_TM_ThresholdBFooter_187

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBBackupEntry188
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthSource184 PSTRTMThresholdDepthProgram185

def result (risk : Rat) (depth : Nat) : PSTRTMThresholdDepthLoopTrace179.Outcome :=
  PSTRTMThresholdDepthLoopTrace179.outcome (PSTRTMThresholdBackup139.depthDigits depth)
    (PaperProofs.Statistics.controllerB risk 1) (initialGap risk)

/-- The first real FALSE is the footer caller's source guard. Everything
else is the SAME exhausted depth, real cleared gap and retained risk. -/
def sourceArchive (risk : Rat) (depth : Nat) : List Bool :=
  false::(PSTRTMThresholdCounterSeek169.gaps (result risk depth).gap++
    (PSTRTMRawNat010.leftBlocks (result risk depth).depth.reverse++false::riskArchive risk))

theorem depth_footer_input (risk : Rat) (depth : Nat) (hd : 1≤depth) :
    (depthFinal risk depth).Tape=Turing.Tape.mk₂ (false::sourceArchive risk depth)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))) := by
  rw [depth_final_tape risk depth hd]
  simp only [PSTRTMThresholdDepthEntry171.initialLeft,PSTRTMThresholdCounterSeek169.gaps,
    sourceArchive,result,List.cons_append]

/-- Fixed1193 labels: the original risk/depth call plus the actual
footer scan/write preparing the existing nearest-field backup ABI.
The copy and allocator themselves are NOT assumed or reimplemented. -/
def entryMachine : Machine 1192 := PSTRTMSeq005.seqMachine depthMachine PSTRTMThresholdBFooter187.footerMachine

def entryTrace (risk : Rat) (depth : Nat) : List (MachineState 1192) :=
  (depthTrace risk depth).map (PSTRTMSeq005.leftCfg (b:=2))++
    (PSTRTMThresholdBFooter187.footerTrace (sourceArchive risk depth) []
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))).map
      (PSTRTMSeq005.rightCfg (a:=1189))

def entryFinal (risk : Rat) (depth : Nat) : MachineState 1192 :=
  PSTRTMSeq005.rightCfg (a:=1189) (PSTRTMThresholdBFooter187.state 2
    (false::(PSTRTMRawNat010.leftBlocks
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)).reverse++
        false::sourceArchive risk depth)) [true])

theorem entry_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1≤depth) :
    Runs entryMachine (encode [.rational risk,.natural depth]) (entryTrace risk depth) (entryFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs depthMachine PSTRTMThresholdBFooter187.footerMachine
    (encode [.rational risk,.natural depth]) (depthFinal risk depth)
    (PSTRTMThresholdBFooter187.state 2
      (false::(PSTRTMRawNat010.leftBlocks
        (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)).reverse++
          false::sourceArchive risk depth)) [true])
    (depthTrace risk depth)
    (PSTRTMThresholdBFooter187.footerTrace (sourceArchive risk depth) []
      (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)))
    (depth_runs risk depth hr hd)
  rw [depth_footer_input risk depth hd]
  exact PSTRTMThresholdBFooter187.footer_runsFrom _ _

theorem entry_final_tape (risk : Rat) (depth : Nat) :
    (entryFinal risk depth).Tape=Turing.Tape.mk₂
      (false::(PSTRTMRawNat010.leftBlocks
        (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)).reverse++
          false::sourceArchive risk depth)) [true] := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBBackupEntry188
