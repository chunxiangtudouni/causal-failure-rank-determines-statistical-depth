module
public import Structure.RootB23_Threshold_OutputArithmetic_OwnedLiteral_005
public import Common.PSTR_TM_ThresholdPredFrame_208

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.OutputArithmetic.OddsFields
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

def right (n : Nat) : List Bool := PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n) ++
  (gap ++ PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload n))

def shiftedCode : Machine 85 := PSTRTMSeq005.seqMachine PSTRTMThresholdPredFrame208.predMachine ReturnHeadroom.twoCode
def copiedCode : Machine 136 := PSTRTMSeq005.seqMachine shiftedCode counterCopyMachine
def movedCode : Machine 556 := PSTRTMSeq005.seqMachine copiedCode fourteenCode
def plantedCode : Machine 605 := PSTRTMSeq005.seqMachine movedCode literalCode
def code : Machine 609 := PSTRTMSeq005.seqMachine plantedCode PSTRTMMulRewind085.rewindMachine

private theorem fee (d n : Nat) (small : n ≤ d) :
    (((((32 * (d + 1) + (20*n+48)) + (4*n^2+22*n+21)) +
      (140*n+336)) + 49) + (2*n+3)) ≤ 1024 * (d+1)^2 := by
  have square := Nat.pow_le_pow_left small 2
  nlinarith only [small,square,Nat.zero_le (d^2)]

/-- D is physically decremented. The two unit fields, three0010 markers,
the copied N and the two extra WEST cells are all actually produced.
No room, N value, footer or copy trace is supplied by the caller. -/
theorem bounded (archive : List Bool) (d : Nat) (positive : 2 ≤ d) :
    BoundedRun code (Tape.mk₂ (false :: archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload d))) 609
      (Tape.mk₂ (false :: false :: false :: archive) (right (d-1)))
      (1024 * (natBits d + 1)^2) := by
  let digits := PSTRTMNatValue017.rawPayload (d-1)
  have predRun := PSTRTMThresholdPredFrame208.pred_runsFrom archive d (by omega)
  have predState : PSTRTMThresholdPredFrame208.predFinal archive d =
      ⟨23,(PSTRTMThresholdPredFrame208.predFinal archive d).Tape⟩ := rfl
  rw [PSTRTMThresholdPredFrame208.pred_final_tape] at predState
  rw [predState] at predRun
  have predBound : BoundedRun PSTRTMThresholdPredFrame208.predMachine
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload d))) 23
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks digits)) (32 * (natBits d+1)) :=
    ⟨PSTRTMThresholdPredFrame208.predTrace archive d,predRun,
      PSTRTMThresholdPredFrame208.pred_length_le archive d (by omega)⟩
  have shifted := ReturnHeadroom.two_bounded archive digits
  have copied := counterCopy_bounded (false :: false :: archive) digits
  simp only [PA17TMRatArithmeticCopy006.workspace,Target.two_right_blanks] at copied
  have moved := fourteen_bounded
    (PA17TMRatArithmeticCopy006.sourceLeft (false :: false :: archive) digits) digits
  have geometry : List.replicate 15 false ++
      PA17TMRatArithmeticCopy006.sourceLeft (false :: false :: archive) digits =
      List.replicate 16 false ++ (PSTRTMRawNat010.leftBlocks digits.reverse ++ false :: false :: false :: archive) := by
    simp only [PA17TMRatArithmeticCopy006.sourceLeft,List.replicate_succ,List.replicate_zero,
      List.cons_append,List.nil_append]
  rw [geometry] at moved
  have planted := literal_bounded
    (PSTRTMRawNat010.leftBlocks digits.reverse ++ false :: false :: false :: archive)
    (PSTRTMIncrement009.blocks digits)
  have returned : BoundedRun PSTRTMMulRewind085.rewindMachine
      (Tape.mk₂ (PSTRTMRawNat010.leftBlocks digits.reverse ++ false :: false :: false :: archive)
        (gap ++ PSTRTMIncrement009.blocks digits)) 3
      (Tape.mk₂ (false :: false :: false :: archive)
        (PSTRTMIncrement009.blocks digits ++ (gap ++ PSTRTMIncrement009.blocks digits)))
      (2*digits.length+3) :=
    ⟨PSTRTMPairRewind105.fullTrace (false :: false :: archive) digits.reverse
      (gap ++ PSTRTMIncrement009.blocks digits),
      PSTRTMPairRewind105.rewind_runsFrom (false :: false :: archive) digits _,
      by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩
  have actual := ((((predBound.seq shifted).seq copied).seq moved).seq planted).seq returned
  have port : PSTRTMSeq005.rightLabel (a := 605) (3 : Fin 4) = (609 : Fin 610) := by decide
  rw [port] at actual
  have length : digits.length = natBits (d-1) := by simp only [digits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have small := PSTRTMArithmetic008.natBits_mono (Nat.sub_le d 1)
  have cost := fee (natBits d) (natBits (d-1)) small
  rw [← length] at cost
  exact actual.mono cost

end RootB23.Threshold.OutputArithmetic.OddsFields
