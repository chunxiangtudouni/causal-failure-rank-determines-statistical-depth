module

public import Paid.PDROC_BitVM_Native_Store_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.Native.StoreIso

open Turing

variable {K Λ σ υ : Type*} [DecidableEq K]

/-- Store reordering preserves the actual full path, exact cost, labels,
every stack and real HALT. It does not initialize an arbitrary caller
store or prove any source operation without its actual path. -/
theorem actual_trace (iso : σ ≃ υ) (source : Λ → TM2.Stmt (fun _ : K=>Bool) Λ σ)
    (sourceTrace : List (TM2.Cfg (fun _ : K=>Bool) Λ σ))
    (sourceStart sourceFinal : TM2.Cfg (fun _ : K=>Bool) Λ σ)
    (head : sourceTrace.head?=some sourceStart)
    (chain : sourceTrace.IsChain (fun a b=>TM2.step source a=some b))
    (last : sourceTrace.getLast?=some sourceFinal) (halt : TM2.step source sourceFinal=none) :
    ∃ (trace : List (TM2.Cfg (fun _ : K=>Bool) Λ υ)) (final : TM2.Cfg (fun _ : K=>Bool) Λ υ),
      trace.head?=some (cfg iso sourceStart) ∧
      trace.IsChain (fun a b=>TM2.step (machine iso source) a=some b) ∧
      trace.getLast?=some final ∧ TM2.step (machine iso source) final=none ∧
      final.l=sourceFinal.l ∧ final.var=iso sourceFinal.var ∧ final.stk=sourceFinal.stk ∧
      trace.length=sourceTrace.length := by
  refine ⟨sourceTrace.map (cfg iso),cfg iso sourceFinal,?_,?_,?_,?_,rfl,rfl,rfl,?_⟩
  · simp only [List.head?_map,head,Option.map_some]
  · exact List.isChain_map_of_isChain _ (fun a b edge=>by
      rw [step_map,edge]
      rfl) chain
  · simp only [List.getLast?_map,last,Option.map_some]
  · rw [step_map,halt]
    rfl
  · simp only [List.length_map]

end PDROC.BitVM.Native.StoreIso
