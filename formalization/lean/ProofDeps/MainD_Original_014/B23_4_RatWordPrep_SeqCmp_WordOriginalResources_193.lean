module

public import B23_4_RatWordPrep_SeqCmp_WordWholeEnvelope_192
public import B23_4_RatWordPrep_SeqCmp_WordCountToResources_157

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

noncomputable def wholeSpaceCoefficient (C : Type*) : Nat := 1+sourcePushCap C*wholeCoefficient C+sourcePushCap C
noncomputable def wholeClockCoefficient (C : Type*) : Nat := 2*sourceActionCap C*(wholeSpaceCoefficient C+1)
noncomputable def wholeScanCoefficient (C : Type*) : Nat := wholeCoefficient C*wholeClockCoefficient C
noncomputable def wholeChargeCoefficient (C : Type*) : Nat := wholeCoefficient C*(wholeClockCoefficient C+1)

theorem power_positive (C : Type*) (bound : Nat) : 1≤(bound+1)^(wholeDegree C) := by
  simpa only [one_pow] using Nat.pow_le_pow_left (show 1≤bound+1 by omega) (wholeDegree C)

theorem input_le_power (C : Type*) (bound : Nat) : bound≤(bound+1)^(wholeDegree C) :=
  (Nat.le_succ bound).trans (by simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos bound) (wholeDegree_positive C))

theorem space_polynomial (C : Type*) (bound : Nat) :
    bound+sourcePushCap C*(wholeCoefficient C*(bound+1)^(wholeDegree C))+sourcePushCap C≤wholeSpaceCoefficient C*(bound+1)^(wholeDegree C) := by
  have input := input_le_power C bound
  have positive := power_positive C bound
  have paidPush : sourcePushCap C≤sourcePushCap C*(bound+1)^(wholeDegree C) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (sourcePushCap C) positive
  exact (Nat.add_le_add (Nat.add_le_add_right input _) paidPush).trans_eq
    (by unfold wholeSpaceCoefficient; ring)

theorem clock_polynomial (C : Type*) (bound : Nat) :
    2*sourceActionCap C*(bound+sourcePushCap C*(wholeCoefficient C*(bound+1)^(wholeDegree C))+sourcePushCap C+1)≤
      wholeClockCoefficient C*(bound+1)^(wholeDegree C) := by
  have space := space_polynomial C bound
  have positive := power_positive C bound
  have base : bound+sourcePushCap C*(wholeCoefficient C*(bound+1)^(wholeDegree C))+sourcePushCap C+1≤
      (wholeSpaceCoefficient C+1)*(bound+1)^(wholeDegree C) :=
    (Nat.add_le_add space positive).trans_eq (by ring)
  exact (Nat.mul_le_mul_left (2*sourceActionCap C) base).trans_eq (by unfold wholeClockCoefficient; ring)

theorem initial_mass {C : Type*} [Inhabited C] (bits : List Bool) :
    RatInput.occupied (entry (default : C) bits).stk=bits.length := by
  rw [initial_default]
  simp [TM2.init,RatInput.occupied,Fin.sum_univ_succ]

theorem product_power (C : Type*) (a b bound : Nat) :
    (a*(bound+1)^(wholeDegree C))*(b*(bound+1)^(wholeDegree C))=a*b*(bound+1)^(2*wholeDegree C) := by
  rw [two_mul,pow_add]
  ring

/-- Uniform literal-original W/A/P and scanner resources on the complete
actual WORD trace. One fixed positive degree is chosen before inputs;
scanner sum and complete charge use twice that same degree. -/
theorem actual_original_resources (C : Type*) [Inhabited C]
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (run : Segment .halt (entry (default : C) (wordInput E target word)) final),
      final.l=none ∧ TM2.step (program .halt) final=none ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2.2.2)=(default : C) ∧
      final.stk 0=wordOutput E target word ∧ final.stk 3=[] ∧ final.stk 13=[] ∧
      final.stk 15=RatInput.Encoder.packet (E.rationalWordOdds word) [] ∧
      RunBounds .halt run
        (wholeCoefficient C*((wordInput E target word).length+1)^(wholeDegree C))
        (wholeSpaceCoefficient C*((wordInput E target word).length+1)^(wholeDegree C))
        (wholeClockCoefficient C*((wordInput E target word).length+1)^(wholeDegree C)) ∧
      traceClockSum (program .halt) run.trace≤wholeScanCoefficient C*((wordInput E target word).length+1)^(2*wholeDegree C) ∧
      run.trace.length+traceClockSum (program .halt) run.trace≤wholeChargeCoefficient C*((wordInput E target word).length+1)^(2*wholeDegree C) := by
  obtain ⟨final,run,halted,stopped,context,output,empty3,empty13,retained,time⟩ :=
    actual_original_count .halt (default : C) E target word
  let B := (wordInput E target word).length
  have paid := time.trans (original_time_polynomial C E target word)
  have initial : RatInput.occupied (entry (default : C) (wordInput E target word)).stk≤B := (initial_mass _).le
  have raw := count_to_resources run B (wholeCoefficient C*(B+1)^(wholeDegree C)) initial paid
  have bounds := raw.mono (Nat.le_refl _) (space_polynomial C B) (clock_polynomial C B)
  refine ⟨final,run,halted,stopped,context,output,empty3,empty13,retained,bounds,?_,?_⟩
  · exact bounds.clockSum.trans_eq (product_power C (wholeCoefficient C) (wholeClockCoefficient C) B)
  · have positive := power_positive C B
    have clock : wholeClockCoefficient C*(B+1)^(wholeDegree C)+1≤(wholeClockCoefficient C+1)*(B+1)^(wholeDegree C) := by nlinarith
    exact bounds.charge.trans ((Nat.mul_le_mul_left (wholeCoefficient C*(B+1)^(wholeDegree C)) clock).trans_eq
      (product_power C (wholeCoefficient C) (wholeClockCoefficient C+1) B))

end B23_4_RatWordPrep.WordFinish.Resources
