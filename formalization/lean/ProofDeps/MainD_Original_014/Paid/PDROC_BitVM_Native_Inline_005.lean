module

public import Paid.PDROC_BitVM_Native_Lift_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.BitVM.Native.Inline

open Turing

variable {K Λ Ω σ τ : Type*} [DecidableEq K]

/-- Translate a fixed local subroutine into caller labels. Its halt becomes
an actual goto to the return label; caller store is preserved. All stores
used by the eventual Bool machine must be fixed finite types. -/
def statement (labels : Λ → Ω) (returnLabel : Ω) :
    TM2.Stmt (fun _ : K=>Bool) Λ σ → TM2.Stmt (fun _ : K=>Bool) Ω (σ×τ)
  | .push k value next => .push k (fun s=>value s.1) (statement labels returnLabel next)
  | .peek k value next => .peek k (fun s bit=>(value s.1 bit,s.2)) (statement labels returnLabel next)
  | .pop k value next => .pop k (fun s bit=>(value s.1 bit,s.2)) (statement labels returnLabel next)
  | .load value next => .load (fun s=>(value s.1,s.2)) (statement labels returnLabel next)
  | .branch test yes no => .branch (fun s=>test s.1)
      (statement labels returnLabel yes) (statement labels returnLabel no)
  | .goto target => .goto (fun s=>labels (target s.1))
  | .halt => .goto (fun _=>returnLabel)

def cfg (labels : Λ → Ω) (returnLabel : Ω) (extra : τ)
    (state : TM2.Cfg (fun _ : K=>Bool) Λ σ) : TM2.Cfg (fun _ : K=>Bool) Ω (σ×τ) :=
  ⟨some (state.l.map labels |>.getD returnLabel),(state.var,extra),state.stk⟩

/-- Exact stepAux equality, including the last real local halt instruction
translated into a real return jump. -/
theorem stepAux_map (labels : Λ → Ω) (returnLabel : Ω)
    (code : TM2.Stmt (fun _ : K=>Bool) Λ σ) (store : σ) (extra : τ)
    (contents : K → List Bool) :
    TM2.stepAux (statement labels returnLabel code) (store,extra) contents=
      cfg labels returnLabel extra (TM2.stepAux code store contents) := by
  induction code generalizing store contents with
  | push k value next ih => exact ih _ _
  | peek k value next ih => exact ih _ _
  | pop k value next ih => exact ih _ _
  | load value next ih => exact ih _ _
  | branch test yes no ihYes ihNo =>
    cases selected : test store
    · simpa only [statement,TM2.stepAux,selected,Bool.cond_false] using ihNo store contents
    · simpa only [statement,TM2.stepAux,selected,Bool.cond_true] using ihYes store contents
  | goto target => rfl
  | halt => rfl

/-- Caller instructions outside the selected local labels are arbitrary.
The theorem does not execute their host semantics as a machine step. -/
theorem step_edge (labels : Λ → Ω) (returnLabel : Ω)
    (source : Λ → TM2.Stmt (fun _ : K=>Bool) Λ σ)
    (caller : Ω → TM2.Stmt (fun _ : K=>Bool) Ω (σ×τ))
    (agrees : ∀ label,caller (labels label)=statement labels returnLabel (source label))
    (before after : TM2.Cfg (fun _ : K=>Bool) Λ σ) (extra : τ)
    (actual : TM2.step source before=some after) :
    TM2.step caller (cfg labels returnLabel extra before)=some (cfg labels returnLabel extra after) := by
  rcases before with ⟨label,store,contents⟩
  cases label with
  | none => cases actual
  | some label =>
    have next : TM2.stepAux (source label) store contents=after := Option.some.inj actual
    change some (TM2.stepAux (caller (labels label)) (store,extra) contents)=_
    rw [agrees,stepAux_map,next]

omit [DecidableEq K] in
theorem supports_statement (labels : Λ → Ω) (returnLabel : Ω)
    (localSupport : Finset Λ) (callerSupport : Finset Ω)
    (closedLabels : ∀ label∈localSupport,labels label∈callerSupport)
    (closedReturn : returnLabel∈callerSupport)
    (code : TM2.Stmt (fun _ : K=>Bool) Λ σ) (closed : TM2.SupportsStmt localSupport code) :
    TM2.SupportsStmt callerSupport (statement (τ:=τ) labels returnLabel code) := by
  induction code with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih closed
  | branch _ _ _ ihYes ihNo => exact ⟨ihYes closed.1,ihNo closed.2⟩
  | goto target => exact fun store=>closedLabels _ (closed store.1)
  | halt => exact fun _=>closedReturn

end PDROC.BitVM.Native.Inline
