module

public import Paid.PDROC_BitVM_Native_Inline_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.Native.Inline

open Turing

variable {K Λ Ω σ τ : Type*} [DecidableEq K]

/-- The same genuine local path is a caller path ending at a real return
label, with identical stack data, exact cost and preserved finite caller
store. This does not assert that the entire caller halts. -/
theorem actual_return_trace (labels : Λ → Ω) (returnLabel : Ω)
    (source : Λ → TM2.Stmt (fun _ : K=>Bool) Λ σ)
    (caller : Ω → TM2.Stmt (fun _ : K=>Bool) Ω (σ×τ))
    (agrees : ∀ label,caller (labels label)=statement labels returnLabel (source label))
    (sourceTrace : List (TM2.Cfg (fun _ : K=>Bool) Λ σ))
    (sourceStart sourceFinal : TM2.Cfg (fun _ : K=>Bool) Λ σ) (extra : τ)
    (head : sourceTrace.head?=some sourceStart)
    (chain : sourceTrace.IsChain (fun a b=>TM2.step source a=some b))
    (last : sourceTrace.getLast?=some sourceFinal) (halt : TM2.step source sourceFinal=none) :
    ∃ (trace : List (TM2.Cfg (fun _ : K=>Bool) Ω (σ×τ)))
      (final : TM2.Cfg (fun _ : K=>Bool) Ω (σ×τ)),
      trace.head?=some (cfg labels returnLabel extra sourceStart) ∧
      trace.IsChain (fun a b=>TM2.step caller a=some b) ∧ trace.getLast?=some final ∧
      final.l=some returnLabel ∧ final.stk=sourceFinal.stk ∧
      final.var=(sourceFinal.var,extra) ∧ trace.length=sourceTrace.length := by
  refine ⟨sourceTrace.map (cfg labels returnLabel extra),cfg labels returnLabel extra sourceFinal,
    ?_,?_,?_,?_,rfl,rfl,?_⟩
  · simp only [List.head?_map,head,Option.map_some]
  · exact List.isChain_map_of_isChain _
      (fun a b edge=>step_edge labels returnLabel source caller agrees a b extra edge) chain
  · simp only [List.getLast?_map,last,Option.map_some]
  · rcases sourceFinal with ⟨label,store,contents⟩
    cases label with
    | none => rfl
    | some label => cases halt
  · simp only [List.length_map]

end PDROC.BitVM.Native.Inline
