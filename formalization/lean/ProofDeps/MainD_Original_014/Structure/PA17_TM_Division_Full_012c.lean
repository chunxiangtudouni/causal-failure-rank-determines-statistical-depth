module
public import Structure.PA17_TM_Division_Full_012b
public import Structure.PA17_TM_Division_Bounds_008a

/-! The original all-input quotient/remainder theorem, on the same actual
long-division run, with full raw parse, moves, cleanup, HALT and visitedSpace. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionFull012

open PA17TMDivisionFront007 PA17TMDivisionFrontLayout011
open PA17TMDivisionLoop002 PA17TMDivisionCodec003
open PSTRTMBinaryAdd024 PSTRTMIncrement009

def quotientTrace (a b : Nat) (kernelTrace : List (MachineState 577)) : List (MachineState 1136) :=
  (commonTrace a b kernelTrace).map (PSTRTMSeq005.leftCfg (b := 140)) ++
    (quotientTailTrace (resultArchive a b) (resultResident a b)).map (PSTRTMSeq005.rightCfg (a := 995))

def remainderTrace (a b : Nat) (kernelTrace : List (MachineState 577)) : List (MachineState 1113) :=
  (commonTrace a b kernelTrace).map (PSTRTMSeq005.leftCfg (b := 117)) ++
    (remainderTailTrace (PSTRTMPackLoop043.pairedDigits (resultArchive a b)) (resultResident a b)).map
      (PSTRTMSeq005.rightCfg (a := 995))

theorem quotientTrace_length (a b : Nat) (kernelTrace : List (MachineState 577)) :
    (quotientTrace a b kernelTrace).length = (commonTrace a b kernelTrace).length +
      (quotientTailTrace (resultArchive a b) (resultResident a b)).length := by
  change ((commonTrace a b kernelTrace).map (PSTRTMSeq005.leftCfg (a := 995) (b := 140)) ++
    (quotientTailTrace (resultArchive a b) (resultResident a b)).map
      (PSTRTMSeq005.rightCfg (a := 995) (b := 140))).length = _
  rw [List.length_append]
  exact congrArg₂ Nat.add (List.length_map (PSTRTMSeq005.leftCfg (a := 995) (b := 140)))
    (List.length_map (PSTRTMSeq005.rightCfg (a := 995) (b := 140)))

theorem remainderTrace_length (a b : Nat) (kernelTrace : List (MachineState 577)) :
    (remainderTrace a b kernelTrace).length = (commonTrace a b kernelTrace).length +
      (remainderTailTrace (PSTRTMPackLoop043.pairedDigits (resultArchive a b)) (resultResident a b)).length := by
  change ((commonTrace a b kernelTrace).map (PSTRTMSeq005.leftCfg (a := 995) (b := 117)) ++
    (remainderTailTrace (PSTRTMPackLoop043.pairedDigits (resultArchive a b)) (resultResident a b)).map
      (PSTRTMSeq005.rightCfg (a := 995) (b := 117))).length = _
  rw [List.length_append]
  exact congrArg₂ Nat.add (List.length_map (PSTRTMSeq005.leftCfg (a := 995) (b := 117)))
    (List.length_map (PSTRTMSeq005.rightCfg (a := 995) (b := 117)))

theorem quotient_remainder_computes (a b : Nat) :
    computes quotientMachine (encodeNat a ++ encodeNat b) (encodeNat (a/b))
      (32768*(natBits a+natBits b+1)^2) (32768*(natBits a+natBits b+1)^2) ∧
    computes remainderMachine (encodeNat a ++ encodeNat b) (encodeNat (a%b))
      (32768*(natBits a+natBits b+1)^2) (32768*(natBits a+natBits b+1)^2) := by
  obtain ⟨kernelTrace,hkernel,hq,hr,hql,hrl,hkt⟩ := original_kernel a b
  have hc := common_runs_from_kernel a b kernelTrace hkernel
  have hqValue : firstValue (resultArchive a b) = a/b := by
    rw [resultArchive,archiveFor_done_firstValue,hq]
  have hal := resultArchive_length a b hql
  have qTailRun := quotientTail_from_resident (resultArchive a b) (resultResident a b)
  rw [← commonFinal_tape a b] at qTailRun
  have rTailRun := remainderTail_from_resident (resultArchive a b) (resultResident a b)
  rw [← commonFinal_tape a b] at rTailRun
  have qRun := PSTRTMSeq005.seq_runs commonMachine quotientTailMachine (encodeNat a ++ encodeNat b)
    (commonFinal a b) (quotientTailFinal (resultArchive a b))
    (commonTrace a b kernelTrace) (quotientTailTrace (resultArchive a b) (resultResident a b)) hc qTailRun
  have rRun := PSTRTMSeq005.seq_runs commonMachine remainderTailMachine (encodeNat a ++ encodeNat b)
    (commonFinal a b) (remainderTailFinal (resultResident a b))
    (commonTrace a b kernelTrace)
    (remainderTailTrace (PSTRTMPackLoop043.pairedDigits (resultArchive a b)) (resultResident a b)) hc rTailRun
  have qWhole : (quotientTailFinal (resultArchive a b)).Tape = Turing.Tape.mk₁ (encodeNat (a/b)) := by
    rw [quotientTail_final_tape,hqValue]
  have rWhole : (remainderTailFinal (resultResident a b)).Tape = Turing.Tape.mk₁ (encodeNat (a%b)) := by
    rw [remainderTail_final_tape,hr]
  have qTailLength : (quotientTailTrace (resultArchive a b) (resultResident a b)).length ≤
      256*(max (natBits a) (natBits b)+2)^2 := by
    have h := quotientTailTrace_length_le (resultArchive a b) (resultResident a b)
    simp only [hal,hrl] at h
    exact h.trans (PA17TMDivisionBounds008.quotient_postlude_bound _)
  have rTailLength : (remainderTailTrace (PSTRTMPackLoop043.pairedDigits (resultArchive a b)) (resultResident a b)).length ≤
      256*(max (natBits a) (natBits b)+2)^2 := by
    have h := remainder_from_resident_length_le (resultArchive a b) (resultResident a b)
    simp only [hal,hrl] at h
    exact h.trans (PA17TMDivisionBounds008.remainder_postlude_bound _)
  have qLength : (quotientTrace a b kernelTrace).length ≤ 8192*(natBits a+natBits b+1)^2 := by
    rw [quotientTrace_length,commonTrace_length]
    exact PA17TMDivisionBounds008.complete_trace_bound _ _ _ _ _ (original_max_room a b)
      (frontTrace_length_le a b) hkt qTailLength
  have rLength : (remainderTrace a b kernelTrace).length ≤ 8192*(natBits a+natBits b+1)^2 := by
    rw [remainderTrace_length,commonTrace_length]
    exact PA17TMDivisionBounds008.complete_trace_bound _ _ _ _ _ (original_max_room a b)
      (frontTrace_length_le a b) hkt rTailLength
  have inputLength : (encodeNat a ++ encodeNat b).length ≤ 2*(natBits a+natBits b+1) :=
    (originalInput_length a b).le
  have timeRelax : 8192*(natBits a+natBits b+1)^2 ≤ 32768*(natBits a+natBits b+1)^2 :=
    Nat.mul_le_mul_right _ (by decide : 8192 ≤ 32768)
  constructor
  · refine ⟨quotientTrace a b kernelTrace,
      PSTRTMSeq005.rightCfg (a := 995) (quotientTailFinal (resultArchive a b)),qRun,?_,qLength.trans timeRelax,?_⟩
    · change (quotientTailFinal (resultArchive a b)).Tape.right₀ = _
      rw [qWhole]
      exact Turing.Tape.mk'_right₀ _ _
    · exact PA17TMDivisionBounds008.original_visitedSpace_bound quotientMachine
        (encodeNat a ++ encodeNat b).length (natBits a+natBits b+1)
        (quotientTrace a b kernelTrace) (originalSize_positive a b) inputLength qLength
  · refine ⟨remainderTrace a b kernelTrace,
      PSTRTMSeq005.rightCfg (a := 995) (remainderTailFinal (resultResident a b)),rRun,?_,rLength.trans timeRelax,?_⟩
    · change (remainderTailFinal (resultResident a b)).Tape.right₀ = _
      rw [rWhole]
      exact Turing.Tape.mk'_right₀ _ _
    · exact PA17TMDivisionBounds008.original_visitedSpace_bound remainderMachine
        (encodeNat a ++ encodeNat b).length (natBits a+natBits b+1)
        (remainderTrace a b kernelTrace) (originalSize_positive a b) inputLength rLength

/-- Fixed finite code and positive constants precede EVERY original pair
of naturals. Both original encodings and b=0 are included without premises. -/
theorem original_div_mod :
    ∃ (statesQ statesR c d : Nat) (qM : Machine statesQ) (rM : Machine statesR),
      0<c ∧ 0<d ∧ ∀ a b : Nat,
        computes qM (encodeNat a ++ encodeNat b) (encodeNat (a/b))
          (c*(natBits a+natBits b+1)^d) (c*(natBits a+natBits b+1)^d) ∧
        computes rM (encodeNat a ++ encodeNat b) (encodeNat (a%b))
          (c*(natBits a+natBits b+1)^d) (c*(natBits a+natBits b+1)^d) :=
  ⟨1136,1113,32768,2,quotientMachine,remainderMachine,by decide,by decide,quotient_remainder_computes⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionFull012
