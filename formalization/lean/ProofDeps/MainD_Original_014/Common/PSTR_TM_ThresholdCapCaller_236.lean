module
public import Common.PSTR_TM_ThresholdCapRun_235

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapCaller236
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCapCode234 PSTRTMThresholdCapRun235 PSTRTMThresholdBDatum224

/-! Fixed original[q,1] call -> real cap TRUE/FALSE HALT control. q is
retained in the literal B engine archive, but restoring a raw q packet
for the uncapped branch is NOT free. A surrounding RawMul caller must
really retain/recover q, marshal[q,1], call and consume the branch.
No such caller I/O or original five-Datum output is claimed here. -/

def capMachine : Machine 1321 := PSTRTMSeq005.seqMachine datumMachine classifyMachine

private theorem scale_cube (input : Nat) : input+1 ≤ (input+2)^3 := by
  have hs : 1 ≤ input+2 := by omega
  have hp := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hp
  omega

/-- Code/capacity precede ALL positive q. The original threshold caller
derives positivity from its legal risk and actual positive integer factor;
no extra original eligibility, branch certificate or width is introduced. -/
theorem original_capFlag_contract (q : Rat) (hq : 0 < q) :
    ∃ trace last distance,
      Runs capMachine (encode [.rational q,.natural 1]) trace last ∧
      last.q = PSTRTMSeq005.rightLabel (a := 1314) (if (1/4 : Rat) ≤ q then (5 : Fin 7) else 6) ∧
      distance ≤ 4 ∧
      last.Tape = rightSteps distance (Turing.Tape.mk₂ (PSTRTMThresholdBReblock195.savedLeft q 1)
        (encodeDatum (.natural (PaperProofs.Statistics.controllerB q 1)))) ∧
      trace.length ≤ 67108864*((encode [.rational q,.natural 1]).length+2)^3 ∧
      ∀ clock, visitedSpace capMachine (encode [.rational q,.natural 1]).length (trace.take clock) ≤
        268435456*((encode [.rational q,.natural 1]).length+2)^3 := by
  obtain ⟨part,exit,distance,hpart,hflag,ht,hd,htape⟩ := datum_classify_contract
    (PaperProofs.Statistics.controllerB q 1) (PSTRTMThresholdBReblock195.savedLeft q 1) []
  let trace := (datumTrace q 1).map (PSTRTMSeq005.leftCfg (b := 6)) ++
    part.map (PSTRTMSeq005.rightCfg (a := 1314))
  let last := PSTRTMSeq005.rightCfg (a := 1314) exit
  have hrun : Runs capMachine (encode [.rational q,.natural 1]) trace last := by
    apply PSTRTMSeq005.seq_runs datumMachine classifyMachine
      (encode [.rational q,.natural 1]) (datumFinal q 1) exit (datumTrace q 1) part
      (datum_runs q 1 hq (by decide))
    rw [datum_final_tape]
    simpa only [List.append_nil] using hpart
  have hcontrol : last.q = PSTRTMSeq005.rightLabel (a := 1314)
      (if (1/4 : Rat) ≤ q then (5 : Fin 7) else 6) := by
    have hf : exit.q = (if (1/4 : Rat) ≤ q then (5 : Fin 7) else 6) := by
      simpa only [B_one_le_two_iff q hq] using hflag
    exact congrArg (PSTRTMSeq005.rightLabel (a := 1314)) hf
  have hout : last.Tape = rightSteps distance
      (Turing.Tape.mk₂ (PSTRTMThresholdBReblock195.savedLeft q 1)
        (encodeDatum (.natural (PaperProofs.Statistics.controllerB q 1)))) := by
    change exit.Tape = _
    simpa only [List.append_nil] using htape
  have htime : trace.length ≤ 67108864*((encode [.rational q,.natural 1]).length+2)^3 := by
    have hm := datum_time_le q 1 hq (by decide)
    change (datumTrace q 1).length ≤ 33554432*((encode [.rational q,.natural 1]).length+2)^3 at hm
    have hc := scale_cube (encode [.rational q,.natural 1]).length
    simp only [trace,List.length_append,List.length_map]
    omega
  refine ⟨trace,last,distance,hrun,hcontrol,hd,hout,htime,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le capMachine (encode [.rational q,.natural 1]).length (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hc := scale_cube (encode [.rational q,.natural 1]).length
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapCaller236
