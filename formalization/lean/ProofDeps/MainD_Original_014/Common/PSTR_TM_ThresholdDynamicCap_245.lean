module
public import Common.PSTR_TM_ThresholdCapBranch_244

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDynamicCap245
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdBDatum224

/-! A fixed actual dynamic branch on ORIGINAL[q,1], for ALL positive q.
The cap branch produces canonical quarter Datum; the uncapped branch
preserves its B scratch Datum and the entire q archive at the same head.
The real subsequent q recovery/uncapped output is still required. -/

def dynamicMachine : Machine 1365 := PSTRTMSeq005.seqMachine datumMachine
  PSTRTMThresholdCapBranch244.branchMachine

def final (q : Rat) : MachineState 1365 := PSTRTMSeq005.rightCfg (a := 1314)
  (PSTRTMThresholdCapBranch244.final (PSTRTMThresholdBReblock195.savedLeft q 1)
    (PaperProofs.Statistics.controllerB q 1))

theorem final_tape (q : Rat) (hq : 0 < q) : (final q).Tape =
    Turing.Tape.mk₂ (PSTRTMThresholdBReblock195.savedLeft q 1)
      (if (1/4 : Rat) ≤ q then encodeDatum (.rational (1/4 : Rat))
       else encodeDatum (.natural (PaperProofs.Statistics.controllerB q 1))) := by
  change (PSTRTMThresholdCapBranch244.final _ _).Tape = _
  rw [PSTRTMThresholdCapBranch244.final_tape]
  simp only [PSTRTMThresholdCapCode234.B_one_le_two_iff q hq]

theorem final_control (q : Rat) (hq : 0 < q) : (final q).q.val =
    if (1/4 : Rat) ≤ q then 1365 else 1330 := by
  change 1315+(PSTRTMThresholdCapBranch244.final _ _).q.val = _
  rw [PSTRTMThresholdCapBranch244.final_control]
  simp only [PSTRTMThresholdCapCode234.B_one_le_two_iff q hq]
  split <;> rfl

private theorem scale_cube (input : Nat) : input+1 ≤ (input+2)^3 := by
  have hs : 1 ≤ input+2 := by omega
  have hp := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hp
  omega

theorem original_dynamicCap_contract (q : Rat) (hq : 0 < q) :
    ∃ trace,
      Runs dynamicMachine (encode [.rational q,.natural 1]) trace (final q) ∧
      trace.length ≤ 67108864*((encode [.rational q,.natural 1]).length+2)^3 ∧
      ∀ clock, visitedSpace dynamicMachine (encode [.rational q,.natural 1]).length (trace.take clock) ≤
        268435456*((encode [.rational q,.natural 1]).length+2)^3 := by
  obtain ⟨part,callee,time⟩ := PSTRTMThresholdCapBranch244.datum_branch_contract
    (PSTRTMThresholdBReblock195.savedLeft q 1) (PaperProofs.Statistics.controllerB q 1)
  let trace := (datumTrace q 1).map (PSTRTMSeq005.leftCfg (b := 50)) ++
    part.map (PSTRTMSeq005.rightCfg (a := 1314))
  have actual : Runs dynamicMachine (encode [.rational q,.natural 1]) trace (final q) := by
    apply PSTRTMSeq005.seq_runs datumMachine PSTRTMThresholdCapBranch244.branchMachine
      (encode [.rational q,.natural 1]) (datumFinal q 1)
      (PSTRTMThresholdCapBranch244.final (PSTRTMThresholdBReblock195.savedLeft q 1)
        (PaperProofs.Statistics.controllerB q 1)) (datumTrace q 1) part (datum_runs q 1 hq (by decide))
    rw [datum_final_tape]
    exact callee
  have actualTime : trace.length ≤ 67108864*((encode [.rational q,.natural 1]).length+2)^3 := by
    have hm := datum_time_le q 1 hq (by decide)
    change (datumTrace q 1).length ≤ 33554432*((encode [.rational q,.natural 1]).length+2)^3 at hm
    have hc := scale_cube (encode [.rational q,.natural 1]).length
    simp only [trace,List.length_append,List.length_map]
    omega
  refine ⟨trace,actual,actualTime,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le dynamicMachine (encode [.rational q,.natural 1]).length (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hc := scale_cube (encode [.rational q,.natural 1]).length
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDynamicCap245
