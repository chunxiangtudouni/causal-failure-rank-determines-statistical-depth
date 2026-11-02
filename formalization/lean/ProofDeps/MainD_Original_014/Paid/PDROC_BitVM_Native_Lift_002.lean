module

public import Paid.PDROC_BitVM_Native_Trace_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.Native.Lift

open Turing

variable {I K Λ σ : Type*} [DecidableEq I] [DecidableEq K]

/-- Rename only fixed stack indices. Labels and the finite source store
are unchanged; no unbounded data is introduced into control. -/
def statement (embed : I ↪ K) : TM2.Stmt (fun _ : I => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | .push k value next => .push (embed k) value (statement embed next)
  | .peek k value next => .peek (embed k) value (statement embed next)
  | .pop k value next => .pop (embed k) value (statement embed next)
  | .load value next => .load value (statement embed next)
  | .branch test yes no => .branch test (statement embed yes) (statement embed no)
  | .goto target => .goto target
  | .halt => .halt

def machine (embed : I ↪ K) (source : Λ → TM2.Stmt (fun _ : I => Bool) Λ σ) :
    Λ → TM2.Stmt (fun _ : K => Bool) Λ σ := fun label=>statement embed (source label)

def slots (embed : I ↪ K) (contents : K → List Bool) : I → List Bool := fun k=>contents (embed k)

def cfg (embed : I ↪ K) (state : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : I => Bool) Λ σ := ⟨state.l,state.var,slots embed state.stk⟩

theorem slots_update (embed : I ↪ K) (contents : K → List Bool) (k : I) (word : List Bool) :
    slots embed (Function.update contents (embed k) word)=Function.update (slots embed contents) k word := by
  funext other
  by_cases same : other=k
  · subst other
    simp only [slots,Function.update_self]
  · have different : embed other≠embed k := fun equal=>same (embed.injective equal)
    simp only [slots,Function.update_of_ne different,Function.update_of_ne same]

/-- Exact original TM2 stepAux, after fixed stack-index renaming. -/
theorem stepAux_project (embed : I ↪ K) (code : TM2.Stmt (fun _ : I => Bool) Λ σ)
    (store : σ) (contents : K → List Bool) :
    cfg embed (TM2.stepAux (statement embed code) store contents)=
      TM2.stepAux code store (slots embed contents) := by
  induction code generalizing store contents with
  | push k value next ih =>
    change cfg embed (TM2.stepAux (statement embed next) store
      (Function.update contents (embed k) (value store::contents (embed k))))=_
    rw [ih,slots_update]
    rfl
  | peek k value next ih => exact ih _ _
  | pop k value next ih =>
    change cfg embed (TM2.stepAux (statement embed next) (value store (contents (embed k)).head?)
      (Function.update contents (embed k) (contents (embed k)).tail))=_
    rw [ih,slots_update]
    rfl
  | load value next ih => exact ih _ _
  | branch test yes no ihYes ihNo =>
    cases selected : test store
    · simpa only [statement,TM2.stepAux,selected,Bool.cond_false] using ihNo store contents
    · simpa only [statement,TM2.stepAux,selected,Bool.cond_true] using ihYes store contents
  | goto target => rfl
  | halt => rfl

theorem step_project (embed : I ↪ K) (source : Λ → TM2.Stmt (fun _ : I => Bool) Λ σ)
    (state : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    (TM2.step (machine embed source) state).map (cfg embed)=TM2.step source (cfg embed state) := by
  rcases state with ⟨label,store,contents⟩
  cases label with
  | none => rfl
  | some label =>
    change some (cfg embed (TM2.stepAux (statement embed (source label)) store contents))=_
    rw [stepAux_project]
    rfl

omit [DecidableEq I] in
theorem outside_stepAux (embed : I ↪ K) (code : TM2.Stmt (fun _ : I => Bool) Λ σ)
    (store : σ) (contents : K → List Bool) (other : K) (outside : ∀ k,other≠embed k) :
    (TM2.stepAux (statement embed code) store contents).stk other=contents other := by
  induction code generalizing store contents with
  | push k value next ih =>
    change (TM2.stepAux (statement embed next) store
      (Function.update contents (embed k) (value store::contents (embed k)))).stk other=_
    rw [ih,Function.update_of_ne (outside k)]
  | peek k value next ih => exact ih _ _
  | pop k value next ih =>
    change (TM2.stepAux (statement embed next) (value store (contents (embed k)).head?)
      (Function.update contents (embed k) (contents (embed k)).tail)).stk other=_
    rw [ih,Function.update_of_ne (outside k)]
  | load value next ih => exact ih _ _
  | branch test yes no ihYes ihNo =>
    cases selected : test store
    · simpa only [statement,TM2.stepAux,selected,Bool.cond_false] using ihNo store contents
    · simpa only [statement,TM2.stepAux,selected,Bool.cond_true] using ihYes store contents
  | goto target => rfl
  | halt => rfl

omit [DecidableEq I] [DecidableEq K] in
theorem supports_statement (embed : I ↪ K) (support : Finset Λ)
    (code : TM2.Stmt (fun _ : I => Bool) Λ σ) (closed : TM2.SupportsStmt support code) :
    TM2.SupportsStmt support (statement embed code) := by
  induction code with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih closed
  | branch _ _ _ ihYes ihNo => exact ⟨ihYes closed.1,ihNo closed.2⟩
  | goto _ => exact closed
  | halt => trivial

end PDROC.BitVM.Native.Lift
