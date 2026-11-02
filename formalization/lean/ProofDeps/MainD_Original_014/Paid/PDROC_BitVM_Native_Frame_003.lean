module

public import Paid.PDROC_BitVM_Native_Lift_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Native.Lift

open Turing

variable {I K Λ σ : Type*} [DecidableEq I] [DecidableEq K]

/-- One real renamed source step preserves every other work stack. -/
theorem step_exists (embed : I ↪ K) (source : Λ → TM2.Stmt (fun _ : I => Bool) Λ σ)
    (before : TM2.Cfg (fun _ : K => Bool) Λ σ) (next : TM2.Cfg (fun _ : I => Bool) Λ σ)
    (actual : TM2.step source (cfg embed before)=some next) :
    ∃ after,TM2.step (machine embed source) before=some after ∧ cfg embed after=next ∧
      ∀ other,(∀ k,other≠embed k)→after.stk other=before.stk other := by
  rcases before with ⟨label,store,contents⟩
  cases label with
  | none =>
    simp only [cfg,TM2.step] at actual
    cases actual
  | some label =>
    refine ⟨TM2.stepAux (statement embed (source label)) store contents,rfl,?_,?_⟩
    · have original : TM2.stepAux (source label) store (slots embed contents)=next :=
        Option.some.inj actual
      exact (stepAux_project embed (source label) store contents).trans original
    · intro other outside
      exact outside_stepAux embed (source label) store contents other outside

/-- Lift an existing genuine source path onto fixed work-stack indices.
No archive, scalar value or variable-width object enters control. -/
theorem path (embed : I ↪ K) (source : Λ → TM2.Stmt (fun _ : I => Bool) Λ σ)
    (before : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (oldStart oldFinal : TM2.Cfg (fun _ : I => Bool) Λ σ)
    (rest : List (TM2.Cfg (fun _ : I => Bool) Λ σ))
    (representation : cfg embed before=oldStart)
    (chain : (oldStart::rest).IsChain (fun a b=>TM2.step source a=some b))
    (last : (oldStart::rest).getLast?=some oldFinal) :
    ∃ posts final,posts.length=rest.length ∧
      (before::posts).IsChain (fun a b=>TM2.step (machine embed source) a=some b) ∧
      (before::posts).getLast?=some final ∧ cfg embed final=oldFinal ∧
      ∀ other,(∀ k,other≠embed k)→final.stk other=before.stk other := by
  induction rest generalizing before oldStart with
  | nil =>
    refine ⟨[],before,rfl,List.isChain_singleton _,rfl,?_,?_⟩
    · exact representation.trans (Option.some.inj last)
    · intro other _outside
      rfl
  | cons next rest ih =>
    obtain ⟨edge,tail⟩ := List.isChain_cons_cons.mp chain
    have actual : TM2.step source (cfg embed before)=some next := by rw [representation];exact edge
    obtain ⟨middle,middleStep,middleRep,middleFrame⟩ := step_exists embed source before next actual
    obtain ⟨later,final,length,tailChain,tailLast,finalRep,finalFrame⟩ :=
      ih middle next middleRep tail last
    refine ⟨middle::later,final,?_,List.isChain_cons_cons.mpr ⟨middleStep,tailChain⟩,
      tailLast,finalRep,?_⟩
    · simp only [List.length_cons,length]
    · intro other outside
      exact (finalFrame other outside).trans (middleFrame other outside)

theorem halt_project (embed : I ↪ K) (source : Λ → TM2.Stmt (fun _ : I => Bool) Λ σ)
    (final : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (halt : TM2.step source (cfg embed final)=none) : TM2.step (machine embed source) final=none := by
  rcases final with ⟨label,store,contents⟩
  cases label with
  | none => rfl
  | some label => simp only [cfg,TM2.step,reduceCtorEq] at halt

omit [DecidableEq I] [DecidableEq K] in
theorem supports [Inhabited Λ] (embed : I ↪ K) (source : Λ → TM2.Stmt (fun _ : I => Bool) Λ σ)
    (support : Finset Λ) (closed : TM2.Supports source support) :
    TM2.Supports (machine embed source) support :=
  ⟨closed.1,fun label inside=>supports_statement embed support (source label) (closed.2 label inside)⟩

end PDROC.BitVM.Native.Lift
