module
public import Common.PSTR_TM_ThresholdBReblockCost_196
public import Common.PSTR_TM_ThresholdDenominatorFrame_199

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenominator200
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBReblock195 PSTRTMThresholdDenominatorFrame199

/-- Fixed1355 labels, original input and a retained physical B copy.
No denominator, B, width, workspace or number of iterations is supplied. -/
def targetDenMachine : Machine 1354 := PSTRTMSeq005.seqMachine savedMachine denominatorMachine

def targetDenTrace (risk : Rat) (depth : Nat) : List (MachineState 1354) :=
  (savedTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 62)) ++
    (denominatorTrace (savedLeft risk depth) (PaperProofs.Statistics.controllerB risk depth)).map
      (PSTRTMSeq005.rightCfg (a := 1291))

def targetDenFinal (risk : Rat) (depth : Nat) : MachineState 1354 :=
  PSTRTMSeq005.rightCfg (a := 1291)
    (denominatorFinal (savedLeft risk depth) (PaperProofs.Statistics.controllerB risk depth))

theorem targetDen_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    Runs targetDenMachine (encode [.rational risk,.natural depth])
      (targetDenTrace risk depth) (targetDenFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs savedMachine denominatorMachine
    (encode [.rational risk,.natural depth]) (savedFinal risk depth)
    (denominatorFinal (savedLeft risk depth) (PaperProofs.Statistics.controllerB risk depth))
    (savedTrace risk depth)
    (denominatorTrace (savedLeft risk depth) (PaperProofs.Statistics.controllerB risk depth))
    (saved_runs risk depth hr hd)
  rw [saved_final_tape]
  exact denominator_runsFrom _ _

theorem targetDen_final_tape (risk : Rat) (depth : Nat) :
    (targetDenFinal risk depth).Tape = Turing.Tape.mk₂ (false::savedLeft risk depth)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload
        (4*(PaperProofs.Statistics.controllerB risk depth + 1)))) := by
  change (denominatorFinal _ _).Tape = _
  exact denominator_final_tape _ _

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenominator200
