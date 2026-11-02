module

public import Paid.PDROC_BitVM_Kernel_RawOp_030
public import Structure.PA17_TM_RatArithmetic_RatDivController_070c

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawOp

open Turing PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

/-- The newly frozen original RAW divider satisfies the SAME actual
native-call ABI used by the multiplier. All signs and native zero-divisor
cases are included. Original RAM successful-step conditions stay separate.
The fixed finite machine and constants precede every operand/caller state. -/
theorem actual_div_contract : ∃ states c d : ℕ,∃ source : Machine states,
    0<c ∧ 0<d ∧ NativeContract source (fun x y=>x/y) c d := by
  obtain ⟨states,c,d,source,cPositive,dPositive,contract⟩ :=
    PA17TMRatArithmeticRatDivController070.original_div_exists
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

end PDROC.BitVM.Kernel.RawOp
