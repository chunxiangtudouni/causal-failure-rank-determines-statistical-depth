module

public import Paid.PDROC_BitVM_Kernel_CallFamily_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Source

open Turing PDROC.BitVM.Native

variable {K I : Type*} [DecidableEq K] [DecidableEq I]
variable (Λ σ : I → Type*)

/-- One label family for a fixed source array: local macro labels,
actual returns, and actual entry/reset ports. I and every local type
are fixed before the raw input; no RAM value is a label or store field. -/
abbrev Label := (Sigma Λ) ⊕ (I ⊕ I)
abbrev Store := ∀ index, σ index
abbrev Saved (index : I) := Kernel.CallFamily.Saved σ index

def localLabel (index : I) (label : Λ index) : Label Λ := .inl ⟨index,label⟩
def returnLabel (index : I) : Label Λ := .inr (.inl index)
def entryLabel (index : I) : Label Λ := .inr (.inr index)

def cfg (index : I) (saved : Saved σ index)
    (state : TM2.Cfg (fun _ : K => Bool) (Λ index) (σ index)) :
    TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ) :=
  StoreIso.cfg (Kernel.CallFamily.split σ index)
    (Inline.cfg (localLabel Λ index) (returnLabel Λ index) saved state)

def entryStatement (start : ∀ index, Λ index) (initial : ∀ index, σ index) (index : I) :
    TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ) :=
  .load (fun store => Function.update store index (initial index))
    (.goto (fun _ => localLabel Λ index (start index)))

/-- A single actual finite-control caller. Both reset and every
inter-instruction transfer are real TM2 statements. The caller resume
will be instantiated only with fixed direct literals or actually read
finite branch/indirect flags. It receives no host RAM state. -/
def program (source : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (resume : I → TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ)) :
    Label Λ → TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ)
  | .inl ⟨index,label⟩ => StoreIso.statement (Kernel.CallFamily.split σ index)
      (Inline.statement (localLabel Λ index) (returnLabel Λ index) (source index label))
  | .inr (.inl index) => resume index
  | .inr (.inr index) => entryStatement Λ σ start initial index

def entryState (index : I) (store : Store σ) (contents : K → List Bool) :
    TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ) :=
  ⟨some (entryLabel Λ index),store,contents⟩

def lowerBefore (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (index : I) (contents : K → List Bool) : TM2.Cfg (fun _ : K => Bool) (Λ index) (σ index) :=
  ⟨some (start index),initial index,contents⟩

omit [DecidableEq K] in
theorem initialized_cfg (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (index : I) (store : Store σ) (contents : K → List Bool) :
    cfg Λ σ index (fun other => store other.val) (lowerBefore Λ σ start initial index contents) =
      (⟨some (localLabel Λ index (start index)),Function.update store index (initial index),contents⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ)) := by
  change (⟨some (localLabel Λ index (start index)),
    Kernel.CallFamily.split σ index (initial index,fun other => store other.val),contents⟩ :
    TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ)) = _
  congr 1

theorem entry_edge
    (source : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (resume : I → TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ))
    (index : I) (store : Store σ) (contents : K → List Bool) :
    TM2.step (program Λ σ source start initial resume) (entryState Λ σ index store contents) =
      some (cfg Λ σ index (fun other => store other.val) (lowerBefore Λ σ start initial index contents)) := by
  rw [initialized_cfg]
  rfl

theorem local_edge
    (source : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (resume : I → TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ))
    (index : I) (saved : Saved σ index)
    (before final : TM2.Cfg (fun _ : K => Bool) (Λ index) (σ index))
    (actual : TM2.step (source index) before = some final) :
    TM2.step (program Λ σ source start initial resume) (cfg Λ σ index saved before) =
      some (cfg Λ σ index saved final) := by
  rcases before with ⟨label,finiteStore,contents⟩
  cases label with
  | none => cases actual
  | some label =>
    have transition : TM2.stepAux (source index label) finiteStore contents = final := Option.some.inj actual
    change some (TM2.stepAux
      (StoreIso.statement (Kernel.CallFamily.split σ index)
        (Inline.statement (localLabel Λ index) (returnLabel Λ index) (source index label)))
      ((Kernel.CallFamily.split σ index) (finiteStore,saved)) contents) = _
    rw [StoreIso.stepAux_map,Inline.stepAux_map,transition]
    rfl

/-- The same local macro path is mapped into the fixed whole-program
caller. Its source halt edge reaches a return port; it does not halt
the caller and it does not replace any tape for free. -/
theorem actual_return_trace
    (source : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (resume : I → TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ))
    (index : I) (saved : Saved σ index)
    (run : List (TM2.Cfg (fun _ : K => Bool) (Λ index) (σ index)))
    (before final : TM2.Cfg (fun _ : K => Bool) (Λ index) (σ index))
    (head : run.head? = some before)
    (chain : run.IsChain (fun x y => TM2.step (source index) x = some y))
    (last : run.getLast? = some final) (halt : TM2.step (source index) final = none) :
    ∃ (actual : List (TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ)))
      (returned : TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ)),
      actual.head? = some (cfg Λ σ index saved before) ∧
      actual.IsChain (fun x y => TM2.step (program Λ σ source start initial resume) x = some y) ∧
      actual.getLast? = some returned ∧ returned.l = some (returnLabel Λ index) ∧
      returned.stk = final.stk ∧ returned.var = Kernel.CallFamily.split σ index (final.var,saved) ∧
      actual.length = run.length := by
  have finalLabel : final.l = none := by
    rcases final with ⟨label,finiteStore,contents⟩
    cases label with
    | none => rfl
    | some label => cases halt
  refine ⟨run.map (cfg Λ σ index saved),cfg Λ σ index saved final,?_,?_,?_,?_,rfl,rfl,?_⟩
  · simp only [List.head?_map,head,Option.map_some]
  · exact List.isChain_map_of_isChain _
      (fun x y edge => local_edge Λ σ source start initial resume index saved x y edge) chain
  · simp only [List.getLast?_map,last,Option.map_some]
  · change some (final.l.map (localLabel Λ index) |>.getD (returnLabel Λ index)) = some (returnLabel Λ index)
    rw [finalLabel]
    rfl
  · simp only [List.length_map]

variable [Fintype I] [∀ index, Fintype (Λ index)] [∀ index, Inhabited (Λ index)] [Inhabited I]

omit [DecidableEq K] in
theorem supports
    (source : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (resume : I → TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ))
    (sourceClosed : ∀ index, TM2.Supports (source index) (Finset.univ : Finset (Λ index)))
    (resumeClosed : ∀ index, TM2.SupportsStmt (Finset.univ : Finset (Label Λ)) (resume index)) :
    TM2.Supports (program Λ σ source start initial resume) (Finset.univ : Finset (Label Λ)) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with ⟨index,label⟩ | (index | index)
    · exact StoreIso.supports_statement (Kernel.CallFamily.split σ index) Finset.univ _
        (Inline.supports_statement (localLabel Λ index) (returnLabel Λ index) Finset.univ Finset.univ
          (fun _ _ => Finset.mem_univ _) (Finset.mem_univ _) (source index label)
          ((sourceClosed index).2 label (Finset.mem_univ _)))
    · exact resumeClosed index
    · simp [program,entryStatement,TM2.SupportsStmt]

end PDROC.BitVM.VM.Source
