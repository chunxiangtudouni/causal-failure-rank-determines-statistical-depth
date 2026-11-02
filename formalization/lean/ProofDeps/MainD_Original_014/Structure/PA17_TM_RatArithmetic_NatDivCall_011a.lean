module
public import Structure.PA17_TM_Division_Full_012c

/-! Recover whole canonical tapes for the EXISTING quantified-cost Natdiv
witnesses by deterministic true HALT. No ancestor code, cost or run is changed. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNatDivCall011

open Turing
open PA17TMDivisionFull012 PA17TMDivisionCodec003

theorem div_mod_whole_runs (a b : Nat) :
    (∃ (trace : List (MachineState 1136)) (final : MachineState 1136),
      Runs quotientMachine (encodeNat a++encodeNat b) trace final ∧
      final.Tape = Tape.mk₁ (encodeNat (a/b)) ∧
      trace.length ≤ 32768*(natBits a+natBits b+1)^2 ∧
      visitedSpace quotientMachine (encodeNat a++encodeNat b).length trace ≤
        32768*(natBits a+natBits b+1)^2) ∧
    (∃ (trace : List (MachineState 1113)) (final : MachineState 1113),
      Runs remainderMachine (encodeNat a++encodeNat b) trace final ∧
      final.Tape = Tape.mk₁ (encodeNat (a%b)) ∧
      trace.length ≤ 32768*(natBits a+natBits b+1)^2 ∧
      visitedSpace remainderMachine (encodeNat a++encodeNat b).length trace ≤
        32768*(natBits a+natBits b+1)^2) := by
  obtain ⟨kernelTrace,hkernel,_hq,_hr,_hql,_hrl,_hkt⟩ := original_kernel a b
  have hc := common_runs_from_kernel a b kernelTrace hkernel
  have qTailRun := quotientTail_from_resident (resultArchive a b) (resultResident a b)
  rw [← commonFinal_tape a b] at qTailRun
  have rTailRun := remainderTail_from_resident (resultArchive a b) (resultResident a b)
  rw [← commonFinal_tape a b] at rTailRun
  have qCanonical := PSTRTMSeq005.seq_runs commonMachine quotientTailMachine
    (encodeNat a++encodeNat b) (commonFinal a b) (quotientTailFinal (resultArchive a b))
    (commonTrace a b kernelTrace) (quotientTailTrace (resultArchive a b) (resultResident a b)) hc qTailRun
  have rCanonical := PSTRTMSeq005.seq_runs commonMachine remainderTailMachine
    (encodeNat a++encodeNat b) (commonFinal a b) (remainderTailFinal (resultResident a b))
    (commonTrace a b kernelTrace)
    (remainderTailTrace (PSTRTMPackLoop043.pairedDigits (resultArchive a b)) (resultResident a b)) hc rTailRun
  have qWhole : (PSTRTMSeq005.rightCfg (a:=995) (quotientTailFinal (resultArchive a b))).Tape =
      Tape.mk₁ (encodeNat (a/b)) := by
    change (quotientTailFinal (resultArchive a b)).Tape = _
    rw [quotientTail_final_tape,resultArchive_firstValue]
  have rWhole : (PSTRTMSeq005.rightCfg (a:=995) (remainderTailFinal (resultResident a b))).Tape =
      Tape.mk₁ (encodeNat (a%b)) := by
    change (remainderTailFinal (resultResident a b)).Tape = _
    rw [remainderTail_final_tape,resultResident_firstValue]
  obtain ⟨hqCost,hrCost⟩ := quotient_remainder_computes a b
  obtain ⟨qt,qf,hqRun,_hqOutput,hqTime,hqSpace⟩ := hqCost
  obtain ⟨rt,rf,hrRun,_hrOutput,hrTime,hrSpace⟩ := hrCost
  have eqQ := Part.mem_unique hqRun.2.2.2.2 qCanonical.2.2.2.2
  have eqR := Part.mem_unique hrRun.2.2.2.2 rCanonical.2.2.2.2
  refine ⟨⟨qt,qf,hqRun,?_,hqTime,hqSpace⟩,⟨rt,rf,hrRun,?_,hrTime,hrSpace⟩⟩
  · rw [eqQ]
    exact qWhole
  · rw [eqR]
    exact rWhole

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNatDivCall011
