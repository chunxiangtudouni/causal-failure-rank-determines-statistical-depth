module
public import Structure.PA17_TM_RatArithmetic_NatDivCall_011a
public import Structure.PA17_TM_RatArithmetic_FrameBudget_008a
public import Common.PSTR_TM_Arithmetic_008

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNatDivCall011

open Turing
open PA17TMRatArithmeticFrame005 PA17TMRatArithmeticFrameBudget008

/-- A reusable invocation theorem for BOTH original Natdiv machines.
The displayed physical blank workspace must be produced by the caller.
Neither the code nor the original operand quantifier receives a budget oracle. -/
theorem budget_framed {states : Nat} (machine : Machine states)
    (input output : List Bool) (original : List (MachineState states)) (final : MachineState states)
    (run : Runs machine input original final) (whole : final.Tape = Tape.mk₁ output)
    (budget slack : Nat) (ht : original.length ≤ budget)
    (inputBound : input.length ≤ slack) (outputBound : output.length ≤ slack)
    (archive suffix : List Bool) :
    ∃ (left right : Nat) (framed : List (MachineState states)),
      PSTRTMSeq005.RunsFrom machine
        ⟨0,Tape.mk₂ (List.replicate (budget+slack) false ++ archive)
          (input ++ List.replicate (budget+slack+1-input.length) false ++ suffix)⟩
        framed ⟨final.q,Tape.mk₂ (List.replicate left false ++ archive)
          (output ++ List.replicate (right+1-output.length) false ++ suffix)⟩ ∧
      slack ≤ left ∧ slack ≤ right ∧ framed.length ≤ budget ∧
      framed.map (displacement machine) = original.map (displacement machine) ∧
      left+right = 2*(budget+slack) ∧
      ∀ inputLength, visitedSpace machine inputLength framed ≤ inputLength+2*budget+1 := by
  have runFrom : PSTRTMSeq005.RunsFrom machine (TM0.init input) original final :=
    ⟨run.1,run.2.1,run.2.2.1,run.2.2.2.1⟩
  have room : original.length ≤ budget+slack := by omega
  obtain ⟨left,right,framed,hfrun,hlen,hmap,hsum,hlend,hrend⟩ :=
    frame_runsFrom_budget machine archive suffix original (TM0.init input) final
      (budget+slack) (budget+slack) runFrom room room
  have hl : slack ≤ left := by omega
  have hr : slack ≤ right := by omega
  have inputFits : input.length ≤ budget+slack+1 := by omega
  have outputFits : output.length ≤ right+1 := by omega
  have hi : frameCfg (budget+slack) (budget+slack) archive suffix (TM0.init input) =
      (⟨0,Tape.mk₂ (List.replicate (budget+slack) false ++ archive)
        (input ++ List.replicate (budget+slack+1-input.length) false ++ suffix)⟩ : MachineState states) := by
    unfold frameCfg TM0.init
    rw [frameTape_mk₁ _ _ _ _ _ inputFits]
    simp only [Fin.default_eq_zero]
  have hf : frameCfg left right archive suffix final =
      (⟨final.q,Tape.mk₂ (List.replicate left false ++ archive)
        (output ++ List.replicate (right+1-output.length) false ++ suffix)⟩ : MachineState states) := by
    unfold frameCfg
    rw [whole,frameTape_mk₁ _ _ _ _ _ outputFits]
  rw [hi,hf] at hfrun
  refine ⟨left,right,framed,hfrun,hl,hr,?_,hmap,?_,?_⟩
  · omega
  · omega
  · intro inputLength
    have hs := PSTRTMTrace002.visitedSpace_le machine inputLength framed
    omega

theorem division_output_bits_le (a b : Nat) : natBits (a/b) ≤ natBits a :=
  PSTRTMArithmetic008.natBits_mono (Nat.div_le_self a b)

theorem remainder_output_bits_le (a b : Nat) : natBits (a%b) ≤ natBits a :=
  PSTRTMArithmetic008.natBits_mono (Nat.mod_le a b)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNatDivCall011
