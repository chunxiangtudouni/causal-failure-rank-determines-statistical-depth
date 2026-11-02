module
public import Common.PSTR_TM_ThresholdCapReturn_240

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapResident241
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCapReturn240 PSTRTMThresholdBDatum224

/-! Original[q,1] cap branch with a REAL returned head at its B Datum.
The source q archive and complete B field are unchanged. A caller still
has to retain/recover q, marshal this packet and consume the result; this
does not claim the original five-Datum threshold output or free I/O. -/

def capMachine : Machine 1330 := PSTRTMSeq005.seqMachine datumMachine returnMachine

def final (q : Rat) : MachineState 1330 :=
  PSTRTMSeq005.rightCfg (a := 1314) (b := 15)
    (state (if (1/4 : Rat) ≤ q then 14 else 15) (PSTRTMThresholdBReblock195.savedLeft q 1)
      (encodeDatum (.natural (PaperProofs.Statistics.controllerB q 1))))

theorem final_tape (q : Rat) : (final q).Tape =
    Turing.Tape.mk₂ (PSTRTMThresholdBReblock195.savedLeft q 1)
      (encodeDatum (.natural (PaperProofs.Statistics.controllerB q 1))) := rfl

private theorem scale_cube (input : Nat) : input+1 ≤ (input+2)^3 := by
  have hs : 1 ≤ input+2 := by omega
  have hp := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hp
  omega

theorem original_capResident_contract (q : Rat) (hq : 0 < q) :
    ∃ trace,
      Runs capMachine (encode [.rational q,.natural 1]) trace (final q) ∧
      trace.length ≤ 67108864*((encode [.rational q,.natural 1]).length+2)^3 ∧
      ∀ clock, visitedSpace capMachine (encode [.rational q,.natural 1]).length (trace.take clock) ≤
        268435456*((encode [.rational q,.natural 1]).length+2)^3 := by
  obtain ⟨part,actual,time⟩ := datum_return_contract
    (PaperProofs.Statistics.controllerB q 1) (PSTRTMThresholdBReblock195.savedLeft q 1) []
  let exit := state (if (1/4 : Rat) ≤ q then 14 else 15)
    (PSTRTMThresholdBReblock195.savedLeft q 1)
    (encodeDatum (.natural (PaperProofs.Statistics.controllerB q 1)))
  have callee : PSTRTMSeq005.RunsFrom returnMachine
      ⟨0,(datumFinal q 1).Tape⟩ part exit := by
    rw [datum_final_tape]
    change PSTRTMSeq005.RunsFrom returnMachine
      (state 0 (PSTRTMThresholdBReblock195.savedLeft q 1)
        (encodeDatum (.natural (PaperProofs.Statistics.controllerB q 1)))) part
      (state (if (1/4 : Rat) ≤ q then 14 else 15) (PSTRTMThresholdBReblock195.savedLeft q 1)
        (encodeDatum (.natural (PaperProofs.Statistics.controllerB q 1))))
    simpa only [List.append_nil,PSTRTMThresholdCapCode234.B_one_le_two_iff q hq] using actual
  let trace := (datumTrace q 1).map (PSTRTMSeq005.leftCfg (b := 15)) ++
    part.map (PSTRTMSeq005.rightCfg (a := 1314))
  have actualRun : Runs capMachine (encode [.rational q,.natural 1]) trace (final q) := by
    apply PSTRTMSeq005.seq_runs datumMachine returnMachine
      (encode [.rational q,.natural 1]) (datumFinal q 1) exit (datumTrace q 1) part
      (datum_runs q 1 hq (by decide)) callee
  have actualTime : trace.length ≤ 67108864*((encode [.rational q,.natural 1]).length+2)^3 := by
    have hm := datum_time_le q 1 hq (by decide)
    change (datumTrace q 1).length ≤ 33554432*((encode [.rational q,.natural 1]).length+2)^3 at hm
    have hc := scale_cube (encode [.rational q,.natural 1]).length
    simp only [trace,List.length_append,List.length_map]
    omega
  refine ⟨trace,actualRun,actualTime,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le capMachine (encode [.rational q,.natural 1]).length (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hc := scale_cube (encode [.rational q,.natural 1]).length
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapResident241
