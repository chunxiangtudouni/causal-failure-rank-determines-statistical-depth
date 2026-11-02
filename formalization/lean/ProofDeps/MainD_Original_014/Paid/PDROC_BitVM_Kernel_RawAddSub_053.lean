module

public import Paid.PDROC_BitVM_Kernel_RatInstruction_048
public import Structure.PA17_TM_RatArithmetic_AddSubFull_079a

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawOp

open Turing PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

/-- Reuse ANY fixed original RAW finite Bool machine by its uniform
actual-run contract. The result function occurs only in this proof. -/
theorem native_of_original {states : ℕ} (source : Machine states) (resultFn : Rat → Rat → Rat) (c d : ℕ)
    (contract : ∀ x y : Rat,∃ trace final,Runs source (encode [.rational x,.rational y]) trace final ∧
      final.Tape=Tape.mk₁ (encode [.rational (resultFn x y)]) ∧
      trace.length ≤ c*((encode [.rational x,.rational y]).length+1)^d) :
    NativeContract source resultFn c d := by
  intro x y before active represented
  obtain ⟨old,oldFinal,actual,tape,bound⟩ := contract x y
  obtain ⟨run,final,head,chain,last,halt,representedFinal,size,frame⟩ :=
    actual_workstack_traceFrom Numeric.work source before old
      (TM0.init (encode [.rational x,.rational y])) oldFinal active represented
      actual.1 actual.2.1 actual.2.2.1 actual.2.2.2.1
  refine ⟨run,final,head,chain,last,halt,?_,?_,frame⟩
  · exact (congrArg (fun state : TM0.Cfg Bool (Fin (states+1))=>state.Tape) representedFinal).trans tape
  · rw [size]
    exact Nat.add_le_add_right bound 1

theorem actual_add_contract : ∃ states c d : ℕ,∃ source : Machine states,
    0<c ∧ 0<d ∧ NativeContract source (fun x y=>x+y) c d := by
  obtain ⟨states,c,d,source,positiveC,positiveD,contract⟩ :=
    PA17TMRatArithmeticAddSubFull079.original_add_exists
  refine ⟨states,c,d,source,positiveC,positiveD,native_of_original source (fun x y=>x+y) c d ?_⟩
  intro x y
  obtain ⟨trace,final,run,tape,time,_space⟩ := contract x y
  exact ⟨trace,final,run,tape,time⟩

theorem actual_sub_contract : ∃ states c d : ℕ,∃ source : Machine states,
    0<c ∧ 0<d ∧ NativeContract source (fun x y=>x-y) c d := by
  obtain ⟨states,c,d,source,positiveC,positiveD,contract⟩ :=
    PA17TMRatArithmeticAddSubFull079.original_sub_exists
  refine ⟨states,c,d,source,positiveC,positiveD,native_of_original source (fun x y=>x-y) c d ?_⟩
  intro x y
  obtain ⟨trace,final,run,tape,time,_space⟩ := contract x y
  exact ⟨trace,final,run,tape,time⟩

end PDROC.BitVM.Kernel.RawOp
