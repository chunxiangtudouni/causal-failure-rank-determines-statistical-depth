module

public import Paid.PDROC_BitVM_Native_Return_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.Native.StoreIso

open Turing

variable {K Λ σ υ : Type*} [DecidableEq K]

/-- Reorder fixed finite caller fields, allowing numerical and log routines
to share one fixed product store. The final compiler still requires a
fixed finite store; this operation does not hide unbounded runtime values. -/
def statement (iso : σ ≃ υ) : TM2.Stmt (fun _ : K=>Bool) Λ σ → TM2.Stmt (fun _ : K=>Bool) Λ υ
  | .push k value next => .push k (fun store=>value (iso.symm store)) (statement iso next)
  | .peek k value next => .peek k (fun store bit=>iso (value (iso.symm store) bit)) (statement iso next)
  | .pop k value next => .pop k (fun store bit=>iso (value (iso.symm store) bit)) (statement iso next)
  | .load value next => .load (fun store=>iso (value (iso.symm store))) (statement iso next)
  | .branch test yes no => .branch (fun store=>test (iso.symm store)) (statement iso yes) (statement iso no)
  | .goto target => .goto (fun store=>target (iso.symm store))
  | .halt => .halt

def machine (iso : σ ≃ υ) (source : Λ → TM2.Stmt (fun _ : K=>Bool) Λ σ) :
    Λ → TM2.Stmt (fun _ : K=>Bool) Λ υ := fun label=>statement iso (source label)

def cfg (iso : σ ≃ υ) (state : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    TM2.Cfg (fun _ : K=>Bool) Λ υ := ⟨state.l,iso state.var,state.stk⟩

theorem stepAux_map (iso : σ ≃ υ) (code : TM2.Stmt (fun _ : K=>Bool) Λ σ)
    (store : σ) (contents : K → List Bool) :
    TM2.stepAux (statement iso code) (iso store) contents=
      cfg iso (TM2.stepAux code store contents) := by
  induction code generalizing store contents with
  | push k value next ih =>
    simp only [statement,TM2.stepAux,Equiv.symm_apply_apply]
    exact ih _ _
  | peek k value next ih =>
    simp only [statement,TM2.stepAux,Equiv.symm_apply_apply]
    exact ih _ _
  | pop k value next ih =>
    simp only [statement,TM2.stepAux,Equiv.symm_apply_apply]
    exact ih _ _
  | load value next ih =>
    simp only [statement,TM2.stepAux,Equiv.symm_apply_apply]
    exact ih _ _
  | branch test yes no ihYes ihNo =>
    cases selected : test store
    · simpa only [statement,TM2.stepAux,Equiv.symm_apply_apply,selected,Bool.cond_false] using ihNo store contents
    · simpa only [statement,TM2.stepAux,Equiv.symm_apply_apply,selected,Bool.cond_true] using ihYes store contents
  | goto target => simp only [statement,TM2.stepAux,cfg,Equiv.symm_apply_apply]
  | halt => rfl

theorem step_map (iso : σ ≃ υ) (source : Λ → TM2.Stmt (fun _ : K=>Bool) Λ σ)
    (state : TM2.Cfg (fun _ : K=>Bool) Λ σ) :
    TM2.step (machine iso source) (cfg iso state)=(TM2.step source state).map (cfg iso) := by
  rcases state with ⟨label,store,contents⟩
  cases label with
  | none => rfl
  | some label =>
    change some (TM2.stepAux (statement iso (source label)) (iso store) contents)=_
    rw [stepAux_map]
    rfl

omit [DecidableEq K] in
theorem supports_statement (iso : σ ≃ υ) (support : Finset Λ)
    (code : TM2.Stmt (fun _ : K=>Bool) Λ σ) (closed : TM2.SupportsStmt support code) :
    TM2.SupportsStmt support (statement iso code) := by
  induction code with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih closed
  | branch _ _ _ ihYes ihNo => exact ⟨ihYes closed.1,ihNo closed.2⟩
  | goto target => exact fun store=>closed (iso.symm store)
  | halt => trivial

omit [DecidableEq K] in
theorem supports [Inhabited Λ] (iso : σ ≃ υ)
    (source : Λ → TM2.Stmt (fun _ : K=>Bool) Λ σ) (support : Finset Λ)
    (closed : TM2.Supports source support) : TM2.Supports (machine iso source) support :=
  ⟨closed.1,fun label member=>supports_statement iso support (source label) (closed.2 label member)⟩

theorem initial_map [Inhabited Λ] [Inhabited σ] [Inhabited υ] (iso : σ ≃ υ)
    (sameDefault : iso default=default) (inputStack : K) (input : List Bool) :
    cfg iso (TM2.init (Γ:=fun _ : K=>Bool) (Λ:=Λ) (σ:=σ) inputStack input)=
      TM2.init (Γ:=fun _ : K=>Bool) (Λ:=Λ) (σ:=υ) inputStack input := by
  change (⟨some default,iso default,Function.update (fun _ : K=>([] : List Bool)) inputStack input⟩ :
    TM2.Cfg (fun _ : K=>Bool) Λ υ)=_
  rw [sameDefault]
  rfl

end PDROC.BitVM.Native.StoreIso
