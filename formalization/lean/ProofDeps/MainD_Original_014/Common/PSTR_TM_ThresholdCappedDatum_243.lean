module
public import Common.PSTR_TM_ThresholdCapLiteral_242

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCappedDatum243
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCapLiteral242

/-! Actual original[q,1] -> canonical quarter Datum, for the TRUE cap
branch q>=1/4. This is a branch-specific contract, NOT an added original
caller qualification and NOT the complete badRisk/five-output algorithm.
The fixed code is defined before ALL q, also outside this branch; a full
caller must physically dispatch on the genuine cap control. All q archive
cells survive, while the B(q,1) scratch field is explicitly consumed. -/

def cappedMachine : Machine 1365 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdCapResident241.capMachine quarterMachine

def final (q : Rat) : MachineState 1365 := PSTRTMSeq005.rightCfg (a := 1330) (b := 34)
  (state 34 (PSTRTMThresholdBReblock195.savedLeft q 1) (encodeDatum (.rational (1/4 : Rat))))

theorem final_tape (q : Rat) : (final q).Tape =
    Turing.Tape.mk₂ (PSTRTMThresholdBReblock195.savedLeft q 1) (encodeDatum (.rational (1/4 : Rat))) := rfl

private theorem scale_cube (input : Nat) : input+1 ≤ (input+2)^3 := by
  have hs : 1 ≤ input+2 := by omega
  have hp := Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  simp only [pow_one] at hp
  omega

theorem original_cappedDatum_contract (q : Rat) (hq : 0 < q) (cap : (1/4 : Rat) ≤ q) :
    ∃ trace,
      Runs cappedMachine (encode [.rational q,.natural 1]) trace (final q) ∧
      trace.length ≤ 134217728*((encode [.rational q,.natural 1]).length+2)^3 ∧
      ∀ clock, visitedSpace cappedMachine (encode [.rational q,.natural 1]).length (trace.take clock) ≤
        536870912*((encode [.rational q,.natural 1]).length+2)^3 := by
  obtain ⟨front,actual,time,_space⟩ := PSTRTMThresholdCapResident241.original_capResident_contract q hq
  have small : PaperProofs.Statistics.controllerB q 1 ≤ 2 :=
    (PSTRTMThresholdCapCode234.B_one_le_two_iff q hq).mpr cap
  let part := quarterTrace (PSTRTMThresholdBReblock195.savedLeft q 1) (PaperProofs.Statistics.controllerB q 1)
  have callee : PSTRTMSeq005.RunsFrom quarterMachine
      ⟨0,(PSTRTMThresholdCapResident241.final q).Tape⟩ part
      (state 34 (PSTRTMThresholdBReblock195.savedLeft q 1) (encodeDatum (.rational (1/4 : Rat)))) := by
    rw [PSTRTMThresholdCapResident241.final_tape]
    exact quarter_runsFrom _ _ small
  let trace := front.map (PSTRTMSeq005.leftCfg (b := 34)) ++
    part.map (PSTRTMSeq005.rightCfg (a := 1330))
  have actualRun : Runs cappedMachine (encode [.rational q,.natural 1]) trace (final q) := by
    apply PSTRTMSeq005.seq_runs PSTRTMThresholdCapResident241.capMachine quarterMachine
      (encode [.rational q,.natural 1]) (PSTRTMThresholdCapResident241.final q)
      (state 34 (PSTRTMThresholdBReblock195.savedLeft q 1) (encodeDatum (.rational (1/4 : Rat))))
      front part actual callee
  have actualTime : trace.length ≤ 134217728*((encode [.rational q,.natural 1]).length+2)^3 := by
    have count : part.length = 35 := quarter_length _ _
    have hc := scale_cube (encode [.rational q,.natural 1]).length
    simp only [trace,List.length_append,List.length_map]
    omega
  refine ⟨trace,actualRun,actualTime,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le cappedMachine (encode [.rational q,.natural 1]).length (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hc := scale_cube (encode [.rational q,.natural 1]).length
  omega

theorem original_cappedDatum_computes (q : Rat) (hq : 0 < q) (cap : (1/4 : Rat) ≤ q) :
    computes cappedMachine (encode [.rational q,.natural 1]) (encodeDatum (.rational (1/4 : Rat)))
      (536870912*((encode [.rational q,.natural 1]).length+2)^3)
      (536870912*((encode [.rational q,.natural 1]).length+2)^3) := by
  obtain ⟨trace,actual,time,space⟩ := original_cappedDatum_contract q hq cap
  refine ⟨trace,final q,actual,?_,by omega,?_⟩
  · rw [final_tape]
    simp only [Turing.Tape.mk₂,Turing.Tape.mk'_right₀]
  · simpa only [List.take_length] using space trace.length

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCappedDatum243
