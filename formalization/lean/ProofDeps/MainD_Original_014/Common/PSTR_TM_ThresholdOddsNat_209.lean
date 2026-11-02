module
public import Common.PSTR_TM_ThresholdPredFrame_208
public import Common.PSTR_TM_ThresholdDenominatorCost_201
public import Structure.PA17_TM_RatArithmetic_Unblock_004c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdOddsNat209
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdPredFrame208

private theorem blank_two (bits : List Bool) :
    Turing.ListBlank.mk (bits ++ [false,false]) = Turing.ListBlank.mk bits := by
  calc
    Turing.ListBlank.mk (bits ++ [false,false]) =
        Turing.ListBlank.mk ((bits ++ [false]) ++ [false]) := by rw [List.append_assoc]; rfl
    _ = Turing.ListBlank.mk (bits ++ [false]) := PSTRTMRawNat010.blank_append_false _
    _ = Turing.ListBlank.mk bits := PSTRTMRawNat010.blank_append_false _

theorem pred_inverse_input (archive : List Bool) (value : Nat) :
    (predFinal archive value).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (value - 1)) ++ [false,false]) := by
  rw [pred_final_tape]
  simp only [Turing.Tape.mk₂,blank_two]

def rawPredMachine : Machine 45 :=
  PSTRTMSeq005.seqMachine predMachine PSTRTMUnblock018.unblockMachine

def rawPredTrace (archive : List Bool) (value : Nat) : List (MachineState 45) :=
  (predTrace archive value).map (PSTRTMSeq005.leftCfg (b := 19)) ++
    (PA17TMRatArithmeticUnblock004.framedTrace archive (PSTRTMNatValue017.rawPayload (value - 1)) []).map
      (PSTRTMSeq005.rightCfg (a := 25))

def rawPredFinal (archive : List Bool) (value : Nat) : MachineState 45 :=
  PSTRTMSeq005.rightCfg (a := 25) (PSTRTMUnblock018.state 19 (false::archive) (encodeNat (value - 1) ++ [false]))

theorem rawPred_runsFrom (archive : List Bool) (value : Nat) (hv : 1 < value) :
    PSTRTMSeq005.RunsFrom rawPredMachine
      ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
      (rawPredTrace archive value) (rawPredFinal archive value) := by
  apply PSTRTMSeq005.seq_runsFrom predMachine PSTRTMUnblock018.unblockMachine
    ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value))⟩
    (predFinal archive value)
    (PSTRTMUnblock018.state 19 (false::archive) (encodeNat (value - 1) ++ [false]))
    (predTrace archive value)
    (PA17TMRatArithmeticUnblock004.framedTrace archive (PSTRTMNatValue017.rawPayload (value - 1)) [])
    (pred_runsFrom archive value hv)
  rw [pred_inverse_input]
  exact PA17TMRatArithmeticUnblock004.originalNat_runsFrom _ _ []

theorem rawPred_final_tape (archive : List Bool) (value : Nat) :
    (rawPredFinal archive value).Tape = Turing.Tape.mk₂ (false::archive) (encodeNat (value - 1)) := by
  simp only [rawPredFinal,PSTRTMSeq005.rightCfg,PSTRTMUnblock018.state,Turing.Tape.mk₂,
    PSTRTMRawNat010.blank_append_false]

open PSTRTMThresholdDenominator200

/-- Fixed1401 labels, original risk/depth to canonical raw4*(B+1)-1,
with archived B and risk retained. General Rat arithmetic is not an
opcode, and the physical rational/list serialization remains separate. -/
def oddsNatMachine : Machine 1400 := PSTRTMSeq005.seqMachine targetDenMachine rawPredMachine

def oddsNatTrace (risk : Rat) (depth : Nat) : List (MachineState 1400) :=
  (targetDenTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 45)) ++
    (rawPredTrace (PSTRTMThresholdBReblock195.savedLeft risk depth)
      (4*(PaperProofs.Statistics.controllerB risk depth + 1))).map
      (PSTRTMSeq005.rightCfg (a := 1354))

def oddsNatFinal (risk : Rat) (depth : Nat) : MachineState 1400 :=
  PSTRTMSeq005.rightCfg (a := 1354) (rawPredFinal (PSTRTMThresholdBReblock195.savedLeft risk depth)
    (4*(PaperProofs.Statistics.controllerB risk depth + 1)))

theorem oddsNat_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    Runs oddsNatMachine (encode [.rational risk,.natural depth])
      (oddsNatTrace risk depth) (oddsNatFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs targetDenMachine rawPredMachine
    (encode [.rational risk,.natural depth]) (targetDenFinal risk depth)
    (rawPredFinal (PSTRTMThresholdBReblock195.savedLeft risk depth)
      (4*(PaperProofs.Statistics.controllerB risk depth + 1)))
    (targetDenTrace risk depth)
    (rawPredTrace (PSTRTMThresholdBReblock195.savedLeft risk depth)
      (4*(PaperProofs.Statistics.controllerB risk depth + 1)))
    (targetDen_runs risk depth hr hd)
  rw [targetDen_final_tape]
  exact rawPred_runsFrom _ _ (by omega)

theorem oddsNat_final_tape (risk : Rat) (depth : Nat) :
    (oddsNatFinal risk depth).Tape = Turing.Tape.mk₂ (false::PSTRTMThresholdBReblock195.savedLeft risk depth)
      (encodeNat (4*(PaperProofs.Statistics.controllerB risk depth + 1) - 1)) := by
  change (rawPredFinal _ _).Tape = _
  exact rawPred_final_tape _ _

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdOddsNat209
