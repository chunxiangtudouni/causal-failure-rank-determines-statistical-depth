module

public import Paid.PDROC_BitVM_Native_StoreTrace_013
public import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.CallFamily

open Turing PDROC.BitVM.Native

variable {K I : Type*} [DecidableEq K] [DecidableEq I]
variable (Λ σ : I → Type*)

/-- A source-program-fixed family of heterogeneous finite macro controls.
The final use supplies finite I, every finite label type and every finite
store type before all raw inputs. No operand is kept in this store. -/
abbrev Label := (Sigma Λ) ⊕ I
abbrev Store := ∀ index,σ index
abbrev Saved (index : I) := ∀ other : {j // j ≠ index},σ other.val

def split (index : I) : (σ index × Saved σ index) ≃ Store σ :=
  (Equiv.piSplitAt index σ).symm

def labels (index : I) (label : Λ index) : Label Λ := .inl ⟨index,label⟩
def returnLabel (index : I) : Label Λ := .inr index

def cfg (index : I) (saved : Saved σ index)
    (state : TM2.Cfg (fun _ : K=>Bool) (Λ index) (σ index)) :
    TM2.Cfg (fun _ : K=>Bool) (Label Λ) (Store σ) :=
  StoreIso.cfg (split σ index) (Inline.cfg (labels Λ index) (returnLabel Λ index) saved state)

/-- All source macros share one fixed finite product store. Returning from
a macro takes its actual source halt edge to a real caller return label. -/
def machine (source : ∀ index,Λ index → TM2.Stmt (fun _ : K=>Bool) (Λ index) (σ index))
    (resume : I → TM2.Stmt (fun _ : K=>Bool) (Label Λ) (Store σ)) :
    Label Λ → TM2.Stmt (fun _ : K=>Bool) (Label Λ) (Store σ)
  | .inl ⟨index,label⟩ => StoreIso.statement (split σ index)
      (Inline.statement (labels Λ index) (returnLabel Λ index) (source index label))
  | .inr index => resume index

theorem edge (source : ∀ index,Λ index → TM2.Stmt (fun _ : K=>Bool) (Λ index) (σ index))
    (resume : I → TM2.Stmt (fun _ : K=>Bool) (Label Λ) (Store σ))
    (index : I) (saved : Saved σ index)
    (before final : TM2.Cfg (fun _ : K=>Bool) (Λ index) (σ index))
    (actual : TM2.step (source index) before=some final) :
    TM2.step (machine Λ σ source resume) (cfg Λ σ index saved before)=
      some (cfg Λ σ index saved final) := by
  rcases before with ⟨label,finiteStore,contents⟩
  cases label with
  | none => cases actual
  | some label =>
    have transition : TM2.stepAux (source index label) finiteStore contents=final := Option.some.inj actual
    change some (TM2.stepAux
      (StoreIso.statement (split σ index)
        (Inline.statement (labels Λ index) (returnLabel Λ index) (source index label)))
      ((split σ index) (finiteStore,saved)) contents)=_
    rw [StoreIso.stepAux_map,Inline.stepAux_map,transition]
    rfl

/-- Exact same physical path, without any free initialization or RAM
transition. Entry store and every operand stack are the actual caller ones. -/
theorem actual_return_trace
    (source : ∀ index,Λ index → TM2.Stmt (fun _ : K=>Bool) (Λ index) (σ index))
    (resume : I → TM2.Stmt (fun _ : K=>Bool) (Label Λ) (Store σ))
    (index : I) (saved : Saved σ index)
    (run : List (TM2.Cfg (fun _ : K=>Bool) (Λ index) (σ index)))
    (before final : TM2.Cfg (fun _ : K=>Bool) (Λ index) (σ index))
    (head : run.head?=some before)
    (chain : run.IsChain (fun x y=>TM2.step (source index) x=some y))
    (last : run.getLast?=some final) (halt : TM2.step (source index) final=none) :
    ∃ (actual : List (TM2.Cfg (fun _ : K=>Bool) (Label Λ) (Store σ)))
      (returned : TM2.Cfg (fun _ : K=>Bool) (Label Λ) (Store σ)),
      actual.head?=some (cfg Λ σ index saved before) ∧
      actual.IsChain (fun x y=>TM2.step (machine Λ σ source resume) x=some y) ∧
      actual.getLast?=some returned ∧ returned.l=some (returnLabel Λ index) ∧
      returned.stk=final.stk ∧ returned.var=split σ index (final.var,saved) ∧
      actual.length=run.length := by
  have finalLabel : final.l=none := by
    rcases final with ⟨label,finiteStore,contents⟩
    cases label with
    | none => rfl
    | some label => cases halt
  refine ⟨run.map (cfg Λ σ index saved),cfg Λ σ index saved final,?_,?_,?_,?_,rfl,rfl,?_⟩
  · simp only [List.head?_map,head,Option.map_some]
  · exact List.isChain_map_of_isChain _
      (fun x y step=>edge Λ σ source resume index saved x y step) chain
  · simp only [List.getLast?_map,last,Option.map_some]
  · change some (final.l.map (labels Λ index) |>.getD (returnLabel Λ index))=some (returnLabel Λ index)
    rw [finalLabel]
    rfl
  · simp only [List.length_map]

variable [Fintype I] [∀ index,Fintype (Λ index)] [∀ index,Inhabited (Λ index)] [Inhabited I]

omit [DecidableEq K] in
theorem supports
    (source : ∀ index,Λ index → TM2.Stmt (fun _ : K=>Bool) (Λ index) (σ index))
    (resume : I → TM2.Stmt (fun _ : K=>Bool) (Label Λ) (Store σ))
    (sourceClosed : ∀ index,TM2.Supports (source index) (Finset.univ : Finset (Λ index)))
    (resumeClosed : ∀ index,TM2.SupportsStmt (Finset.univ : Finset (Label Λ)) (resume index)) :
    TM2.Supports (machine Λ σ source resume) (Finset.univ : Finset (Label Λ)) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with ⟨index,label⟩ | index
    · exact StoreIso.supports_statement (split σ index) Finset.univ _
        (Inline.supports_statement (labels Λ index) (returnLabel Λ index) Finset.univ Finset.univ
          (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (source index label)
          ((sourceClosed index).2 label (Finset.mem_univ _)))
    · exact resumeClosed index

end PDROC.BitVM.Kernel.CallFamily
