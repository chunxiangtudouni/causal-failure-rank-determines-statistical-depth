module
public import RootB236_Controller_ResumeErase_Resources004

/-! The caller restores the SAME parent's tools suffix. Child remaining4
is discarded by the actual entry and is never used to re-screen tools. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.ResumeErase
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*} {q : Nat}

def ParentSuffix (eligible remaining : Finset (Fin q)) (tools : List (Fin q)) : Prop :=
  ∃ visited,PaperProofs.Structure.genericRankCandidates q eligible remaining=visited++tools

theorem ParentSuffix.tail {eligible remaining : Finset (Fin q)} {tool : Fin q} {tools : List (Fin q)}
    (suffix : ParentSuffix eligible remaining (tool::tools)) : ParentSuffix eligible remaining tools := by
  obtain ⟨visited,same⟩:=suffix
  refine ⟨visited++[tool],?_⟩
  simpa only [List.append_assoc,List.singleton_append] using same

/-- Seed the continuation invariant from the already proved first SelectErase
return. No candidate is recomputed from the child's remaining. -/
theorem seed_after_head (eligible remaining : Finset (Fin q)) (tool : Fin q) (tail : List Bool)
    (head : (PaperProofs.Structure.genericRankCandidates q eligible remaining).head?=some tool)
    (values : (PaperProofs.Structure.genericRankCandidates q eligible remaining).map Fin.val=
      tool.val::ControllerCandidate.pending (tool.val+1) tail) :
    ∃ tools,ParentSuffix eligible remaining tools ∧
      ControllerCandidate.pending (tool.val+1) tail=tools.map Fin.val := by
  obtain ⟨tools,same⟩:=List.head?_eq_some_iff.mp head
  refine ⟨tools,⟨[tool],same⟩,?_⟩
  rw [same,List.map_cons] at values
  exact (List.cons.inj values).2.symm

def OriginalOutcome (bg : Stack → List Bool) (context : C) (eligible remaining : Finset (Fin q))
    (tools : List (Fin q)) (final : State C) : Prop :=
  (∃ (tool : Fin q) (tail : List Bool) (later : List (Fin q)),tools=tool::later ∧
    ControllerCandidate.pending (tool.val+1) tail=later.map Fin.val ∧ tool.val+1+tail.length=q ∧
    ParentSuffix eligible remaining later ∧
    final=state bg foundPort (context,false,false) tail (EraseSem.mask (remaining.erase tool))
      (ControllerCandidate.unary tool.val) (ControllerCandidate.unary (tool.val+1)) [] (EraseSem.mask remaining).reverse
      (ControllerCandidate.unary q) []) ∨
  (tools=[] ∧ final=state bg emptyPort (context,true,true) [] (EraseSem.mask remaining) []
    (ControllerCandidate.unary q) [] (EraseSem.mask remaining).reverse (ControllerCandidate.unary q) [])

theorem Outcome.original {bg : Stack → List Bool} {context : C} {eligible remaining : Finset (Fin q)}
    {bits : List Bool} {k : Nat} {tools : List (Fin q)} {final : State C}
    (suffix : ParentSuffix eligible remaining tools)
    (represented : ControllerCandidate.pending k bits=tools.map Fin.val)
    (outcome : Outcome bg context bits (EraseSem.mask remaining) k final) :
    OriginalOutcome bg context eligible remaining tools final := by
  rcases outcome with ⟨index,tail,inside,width,selected,ended⟩ | ⟨none,ended⟩
  · have values : tools.map Fin.val=index::ControllerCandidate.pending (index+1) tail := represented.symm.trans selected
    cases tools with
    | nil => cases values
    | cons tool later =>
      obtain ⟨position,pending⟩:=List.cons.inj values
      refine Or.inl ⟨tool,tail,later,rfl,?_,?_,suffix.tail,?_⟩
      · rw [position];exact pending.symm
      · rw [position];simpa only [EraseSem.mask_length] using width
      · rw [←position] at ended
        have erased : SelectErase.eraseMask (EraseSem.mask remaining) tool.val=EraseSem.mask (remaining.erase tool) :=
          SelectErase.eraseMask_original remaining tool
        simpa only [erased,EraseSem.mask_length] using ended
  · refine Or.inr ⟨?_,?_⟩
    · exact List.map_eq_nil_iff.mp (represented.symm.trans none)
    · simpa only [EraseSem.mask_length] using ended

end RootB236.Controller.ResumeErase
