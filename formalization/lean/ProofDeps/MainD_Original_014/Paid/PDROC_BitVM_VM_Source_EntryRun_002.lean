module

public import Paid.PDROC_BitVM_VM_Source_Family_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Source

open Turing PDROC.BitVM.Native

variable {K I : Type*} [DecidableEq K] [DecidableEq I]
variable (Λ σ : I → Type*)

/-- The real entry/reset edge is included in the returned path length.
The initial local store is installed by program, rather than assumed
at the beginning of every simulated source instruction. -/
theorem actual_entry_trace
    (source : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (resume : I → TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ))
    (index : I) (store : Store σ) (contents : K → List Bool)
    (run : List (TM2.Cfg (fun _ : K => Bool) (Λ index) (σ index)))
    (final : TM2.Cfg (fun _ : K => Bool) (Λ index) (σ index))
    (head : run.head? = some (lowerBefore Λ σ start initial index contents))
    (chain : run.IsChain (fun x y => TM2.step (source index) x = some y))
    (last : run.getLast? = some final) (halt : TM2.step (source index) final = none) :
    ∃ (actual : List (TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ)))
      (returned : TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ)),
      actual.head? = some (entryState Λ σ index store contents) ∧
      actual.IsChain (fun x y => TM2.step (program Λ σ source start initial resume) x = some y) ∧
      actual.getLast? = some returned ∧ returned.l = some (returnLabel Λ index) ∧
      returned.stk = final.stk ∧ returned.var = Kernel.CallFamily.split σ index (final.var,fun other => store other.val) ∧
      actual.length = run.length+1 := by
  obtain ⟨mapped,returned,mappedHead,mappedChain,mappedLast,label,data,finiteStore,time⟩ :=
    actual_return_trace Λ σ source start initial resume index (fun other => store other.val)
      run (lowerBefore Λ σ start initial index contents) final head chain last halt
  cases mapped with
  | nil => simp only [List.head?_nil,reduceCtorEq] at mappedHead
  | cons first rest =>
    have firstEq : first = cfg Λ σ index (fun other => store other.val)
        (lowerBefore Λ σ start initial index contents) := Option.some.inj mappedHead
    subst first
    refine ⟨entryState Λ σ index store contents ::
      cfg Λ σ index (fun other => store other.val) (lowerBefore Λ σ start initial index contents) :: rest,
      returned,rfl,?_,?_,label,data,finiteStore,?_⟩
    · exact List.isChain_cons_cons.mpr ⟨entry_edge Λ σ source start initial resume index store contents,mappedChain⟩
    · simpa only [List.getLast?_cons_cons] using mappedLast
    · simp only [List.length_cons] at time ⊢
      omega

theorem direct_return_edge
    (source : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (resume : I → TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ))
    (index next : I)
    (agrees : resume index = .goto (fun _ => entryLabel Λ next))
    (store : Store σ) (contents : K → List Bool) :
    TM2.step (program Λ σ source start initial resume)
      (⟨some (returnLabel Λ index),store,contents⟩ : TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ)) =
      some (entryState Λ σ next store contents) := by
  change some (TM2.stepAux (resume index) store contents) = _
  rw [agrees]
  rfl

theorem halt_return_edge
    (source : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (resume : I → TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ))
    (index : I) (agrees : resume index = .halt)
    (store : Store σ) (contents : K → List Bool) :
    TM2.step (program Λ σ source start initial resume)
      (⟨some (returnLabel Λ index),store,contents⟩ : TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ)) =
      some ⟨none,store,contents⟩ := by
  change some (TM2.stepAux (resume index) store contents) = _
  rw [agrees]
  rfl

/-- Appending the actual fetched-halt return produces the true caller
HALT, on the same stacks and store. No eval/output is assumed here. -/
theorem actual_entry_halt_trace
    (source : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (start : ∀ index, Λ index) (initial : ∀ index, σ index)
    (resume : I → TM2.Stmt (fun _ : K => Bool) (Label Λ) (Store σ))
    (index : I) (agrees : resume index = .halt) (store : Store σ) (contents : K → List Bool)
    (run : List (TM2.Cfg (fun _ : K => Bool) (Λ index) (σ index)))
    (final : TM2.Cfg (fun _ : K => Bool) (Λ index) (σ index))
    (head : run.head? = some (lowerBefore Λ σ start initial index contents))
    (chain : run.IsChain (fun x y => TM2.step (source index) x = some y))
    (last : run.getLast? = some final) (halt : TM2.step (source index) final = none) :
    ∃ (actual : List (TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ)))
      (terminal : TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ)),
      actual.head? = some (entryState Λ σ index store contents) ∧
      actual.IsChain (fun x y => TM2.step (program Λ σ source start initial resume) x = some y) ∧
      actual.getLast? = some terminal ∧ TM2.step (program Λ σ source start initial resume) terminal = none ∧
      terminal.stk = final.stk ∧ actual.length = run.length+2 := by
  obtain ⟨mapped,returned,mappedHead,mappedChain,mappedLast,label,data,_finiteStore,time⟩ :=
    actual_entry_trace Λ σ source start initial resume index store contents run final head chain last halt
  let terminal : TM2.Cfg (fun _ : K => Bool) (Label Λ) (Store σ) := ⟨none,returned.var,returned.stk⟩
  have edge : TM2.step (program Λ σ source start initial resume) returned = some terminal := by
    rcases returned with ⟨current,finiteStore,physical⟩
    change current = some (returnLabel Λ index) at label
    subst current
    exact halt_return_edge Λ σ source start initial resume index agrees finiteStore physical
  have bridge : [returned,terminal].IsChain
      (fun x y => TM2.step (program Λ σ source start initial resume) x = some y) :=
    List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩
  refine ⟨mapped++[terminal],terminal,?_,?_,List.getLast?_append_cons mapped terminal [],rfl,data,?_⟩
  · simp only [List.head?_append,mappedHead,Option.some_or]
  · exact PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain mapped returned [terminal]
      mappedLast mappedChain bridge
  · simp only [List.length_append,List.length_cons,List.length_nil]
    omega

end PDROC.BitVM.VM.Source
