module

public import Paid.PDROC_BitVM_Kernel_Numeric_001
public import Structure.PA17_TM_RatArithmetic_MulSuffix_063c

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawMul

open Turing PDROC.BitVM.Native
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

/-- This is an existing finite Bool TM0, simulated on two actual global
work stacks. It is not a rational-valued primitive in a transition. -/
def program {states : ℕ} (source : Machine states) := workstackMachine Numeric.work source

theorem supports {states : ℕ} (source : Machine states) :
    TM2.Supports (program source) (Finset.univ : Finset Unit) := workstack_supports Numeric.work source

/-- Reuse the fully frozen original RAW multiplier at its opaque finite
machine ABI, avoiding expansion of its seventeen-component controller.
One native machine and both positive constants precede every operand and
every arbitrary carried caller stack. Entry encoding is to be produced by
CellPair028; it is not an added raw input or supplied answer. -/
theorem fixed_machine :
    ∃ states c d : ℕ,∃ source : Machine states,0<c ∧ 0<d ∧
      ∀ (x y : Rat) (before : TM2.Cfg Numeric.Alphabet Unit (BoolOnStacks.Store states)),
        (Lift.cfg Numeric.work before).l=some () →
        BoolOnStacks.representedState (Lift.cfg Numeric.work before)=TM0.init (encode [.rational x,.rational y]) →
        ∃ (run : List (TM2.Cfg Numeric.Alphabet Unit (BoolOnStacks.Store states)))
          (final : TM2.Cfg Numeric.Alphabet Unit (BoolOnStacks.Store states)),
          run.head?=some before ∧ run.IsChain (fun a b=>TM2.step (program source) a=some b) ∧
          run.getLast?=some final ∧ TM2.step (program source) final=none ∧
          (BoolOnStacks.representedState (Lift.cfg Numeric.work final)).Tape=
            Tape.mk₁ (encode [.rational (x*y)]) ∧
          run.length ≤ c*((encode [.rational x,.rational y]).length+1)^d+1 ∧
          ∀ other,(∀ index,other ≠ Numeric.work index) → final.stk other=before.stk other := by
  obtain ⟨states,c,d,source,cPositive,dPositive,contract⟩ :=
    PA17TMRatArithmeticMulSuffix063.original_mul_exists
  refine ⟨states,c,d,source,cPositive,dPositive,?_⟩
  intro x y before active represented
  obtain ⟨old,oldFinal,actual,tape,bound,_space⟩ := contract x y
  obtain ⟨run,final,head,chain,last,halt,representedFinal,size,frame⟩ :=
    actual_workstack_traceFrom Numeric.work source before old
      (TM0.init (encode [.rational x,.rational y])) oldFinal active represented
      actual.1 actual.2.1 actual.2.2.1 actual.2.2.2.1
  refine ⟨run,final,head,chain,last,halt,?_,?_,frame⟩
  · exact (congrArg (fun state : TM0.Cfg Bool (Fin (states+1))=>state.Tape) representedFinal).trans tape
  · rw [size]
    exact Nat.add_le_add_right bound 1

end PDROC.BitVM.Kernel.RawMul
