module
public import Common.PSTR_TM_ThresholdDenominatorCost_201

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenominatorRaw202
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDenominator200

private theorem blank_two (bits : List Bool) :
    Turing.ListBlank.mk (bits ++ [false,false]) = Turing.ListBlank.mk bits := by
  calc
    Turing.ListBlank.mk (bits ++ [false,false]) =
        Turing.ListBlank.mk ((bits ++ [false]) ++ [false]) := by rw [List.append_assoc]; rfl
    _ = Turing.ListBlank.mk (bits ++ [false]) := PSTRTMRawNat010.blank_append_false _
    _ = Turing.ListBlank.mk bits := PSTRTMRawNat010.blank_append_false _

theorem targetDen_inverse_input (risk : Rat) (depth : Nat) :
    (targetDenFinal risk depth).Tape = Turing.Tape.mk₂
      (false::PSTRTMThresholdBReblock195.savedLeft risk depth)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload
        (4*(PaperProofs.Statistics.controllerB risk depth + 1))) ++ [false,false]) := by
  rw [targetDen_final_tape]
  simp only [Turing.Tape.mk₂,blank_two]

/-- Fixed1375 labels return the canonical raw natural target denominator.
This leaves the original B and risk in the actual left archive and does
not claim the rational target Datum or the five-Datum result is ready. -/
def rawDenMachine : Machine 1374 :=
  PSTRTMSeq005.seqMachine targetDenMachine PSTRTMUnblock018.unblockMachine

def rawDenTrace (risk : Rat) (depth : Nat) : List (MachineState 1374) :=
  (targetDenTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 19)) ++
    (PA17TMRatArithmeticUnblock004.framedTrace (PSTRTMThresholdBReblock195.savedLeft risk depth)
      (PSTRTMNatValue017.rawPayload (4*(PaperProofs.Statistics.controllerB risk depth + 1))) []).map
      (PSTRTMSeq005.rightCfg (a := 1354))

def rawDenFinal (risk : Rat) (depth : Nat) : MachineState 1374 :=
  PSTRTMSeq005.rightCfg (a := 1354) (PSTRTMUnblock018.state 19
    (false::PSTRTMThresholdBReblock195.savedLeft risk depth)
    (encodeNat (4*(PaperProofs.Statistics.controllerB risk depth + 1)) ++ [false]))

theorem rawDen_runs (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    Runs rawDenMachine (encode [.rational risk,.natural depth])
      (rawDenTrace risk depth) (rawDenFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs targetDenMachine PSTRTMUnblock018.unblockMachine
    (encode [.rational risk,.natural depth]) (targetDenFinal risk depth)
    (PSTRTMUnblock018.state 19 (false::PSTRTMThresholdBReblock195.savedLeft risk depth)
      (encodeNat (4*(PaperProofs.Statistics.controllerB risk depth + 1)) ++ [false]))
    (targetDenTrace risk depth)
    (PA17TMRatArithmeticUnblock004.framedTrace (PSTRTMThresholdBReblock195.savedLeft risk depth)
      (PSTRTMNatValue017.rawPayload (4*(PaperProofs.Statistics.controllerB risk depth + 1))) [])
    (targetDen_runs risk depth hr hd)
  rw [targetDen_inverse_input]
  exact PA17TMRatArithmeticUnblock004.originalNat_runsFrom _ _ []

theorem rawDen_final_tape (risk : Rat) (depth : Nat) :
    (rawDenFinal risk depth).Tape = Turing.Tape.mk₂
      (false::PSTRTMThresholdBReblock195.savedLeft risk depth)
      (encodeNat (4*(PaperProofs.Statistics.controllerB risk depth + 1))) := by
  simp only [rawDenFinal,PSTRTMSeq005.rightCfg,PSTRTMUnblock018.state,Turing.Tape.mk₂,
    PSTRTMRawNat010.blank_append_false]

theorem target_denominator_identity (risk : Rat) (depth : Nat) :
    PaperProofs.Statistics.controllerTarget risk depth =
      1 / ((4*(PaperProofs.Statistics.controllerB risk depth + 1) : Nat) : Rat) := by
  unfold PaperProofs.Statistics.controllerTarget
  congr 1
  push_cast
  ring

/-- Exact canonical fields needed by the original target Datum writer.
These are serialization identities; the writer's physical allocation
and movements are still a separate real-machine obligation. -/
theorem target_numerator (risk : Rat) (depth : Nat) :
    (PaperProofs.Statistics.controllerTarget risk depth).num = 1 := by
  rw [target_denominator_identity,one_div]
  exact Rat.inv_natCast_num_of_pos (by omega)

theorem target_denominator (risk : Rat) (depth : Nat) :
    (PaperProofs.Statistics.controllerTarget risk depth).den =
      4*(PaperProofs.Statistics.controllerB risk depth + 1) := by
  rw [target_denominator_identity,one_div]
  exact Rat.inv_natCast_den_of_pos (by omega)

theorem target_datum_bits (risk : Rat) (depth : Nat) :
    encodeDatum (.rational (PaperProofs.Statistics.controllerTarget risk depth)) =
      [true,false] ++ encodeNat 1 ++
        encodeNat (4*(PaperProofs.Statistics.controllerB risk depth + 1)) := by
  have hn : ¬PaperProofs.Statistics.controllerTarget risk depth < 0 :=
    not_lt.mpr (PaperProofs.Statistics.controllerTarget_pos risk depth).le
  simp [encodeDatum,target_numerator,target_denominator,hn]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDenominatorRaw202
