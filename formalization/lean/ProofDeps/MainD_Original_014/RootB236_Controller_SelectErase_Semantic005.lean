module
public import RootB236_Controller_SelectErase_Resources004

/-! Identify the proved physical selection/one-cell overwrite with the
original finRange candidate order and Finset.erase. Masks remain inputs
of this internal physical ABI, not an original-input decoder. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.SelectErase
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*} {q : Nat}

theorem mask_pairs (eligible remaining : Finset (Fin q)) :
    (EraseSem.mask eligible).zip (EraseSem.mask remaining)=ControllerCandidate.incidencePairs eligible remaining := by
  apply List.ext_getElem
  · simp [EraseSem.mask,ControllerCandidate.incidencePairs]
  · intro index left right
    simp [EraseSem.mask,ControllerCandidate.incidencePairs,List.finRange]

theorem original_candidates (eligible remaining : Finset (Fin q)) :
    ControllerCandidate.pending 0 (andBits (EraseSem.mask eligible) (EraseSem.mask remaining))=
      (PaperProofs.Structure.genericRankCandidates q eligible remaining).map Fin.val := by
  rw [andBits,mask_pairs]
  exact ControllerCandidate.original_candidates eligible remaining

theorem eraseMask_original (remaining : Finset (Fin q)) (tool : Fin q) :
    eraseMask (EraseSem.mask remaining) tool.val=EraseSem.mask (remaining.erase tool) :=
  (EraseSem.mask_erase_take_drop remaining tool).symm

theorem selected_head (eligible remaining : Finset (Fin q)) (tool : Nat) (tail : List Nat)
    (inside : tool<q)
    (selected : (PaperProofs.Structure.genericRankCandidates q eligible remaining).map Fin.val=tool::tail) :
    (PaperProofs.Structure.genericRankCandidates q eligible remaining).head?=some ⟨tool,inside⟩ := by
  have head:=congrArg List.head? selected
  rw [List.head?_map] at head
  cases chosen : (PaperProofs.Structure.genericRankCandidates q eligible remaining).head? with
  | none => rw [chosen] at head;cases head
  | some actual =>
    rw [chosen] at head
    have same : actual.val=tool := Option.some.inj head
    have equal : actual=⟨tool,inside⟩ := Fin.ext same
    exact congrArg some equal

def OriginalOutcome (bg : Stack → List Bool) (context : C) (eligible remaining : Finset (Fin q)) (final : State C) : Prop :=
  (∃ (tool : Fin q) (tail : List Bool),
    (PaperProofs.Structure.genericRankCandidates q eligible remaining).head?=some tool ∧
    (PaperProofs.Structure.genericRankCandidates q eligible remaining).map Fin.val=
      tool.val::ControllerCandidate.pending (tool.val+1) tail ∧
    tool.val+1+tail.length=q ∧
    final=state bg .found (context,false,false) tail (EraseSem.mask (remaining.erase tool))
      (ControllerCandidate.unary tool.val) (ControllerCandidate.unary (tool.val+1)) []
      (EraseSem.mask remaining).reverse (ControllerCandidate.unary q) []) ∨
  (PaperProofs.Structure.genericRankCandidates q eligible remaining=[] ∧
    final=state bg .empty (context,true,true) [] (EraseSem.mask remaining) [] (ControllerCandidate.unary q) []
      (EraseSem.mask remaining).reverse (ControllerCandidate.unary q) [])

theorem Outcome.original {bg : Stack → List Bool} {context : C} {eligible remaining : Finset (Fin q)} {final : State C}
    (outcome : Outcome bg context (EraseSem.mask eligible) (EraseSem.mask remaining) final) :
    OriginalOutcome bg context eligible remaining final := by
  rcases outcome with ⟨tool,tail,inside,width,pending,ended⟩ | ⟨pending,ended⟩
  · have range : tool<q := by simpa only [EraseSem.mask_length] using inside
    let selected : Fin q:=⟨tool,range⟩
    have order : (PaperProofs.Structure.genericRankCandidates q eligible remaining).map Fin.val=
        tool::ControllerCandidate.pending (tool+1) tail := (original_candidates eligible remaining).symm.trans pending
    refine Or.inl ⟨selected,tail,selected_head eligible remaining tool _ range order,order,?_,?_⟩
    · simpa only [EraseSem.mask_length] using width
    · have erased : eraseMask (EraseSem.mask remaining) tool=EraseSem.mask (remaining.erase selected) :=
        eraseMask_original remaining selected
      simpa only [erased,EraseSem.mask_length] using ended
  · refine Or.inr ⟨?_,?_⟩
    · have empty : (PaperProofs.Structure.genericRankCandidates q eligible remaining).map Fin.val=[] :=
        (original_candidates eligible remaining).symm.trans pending
      exact List.map_eq_nil_iff.mp empty
    · simpa only [EraseSem.mask_length] using ended

end RootB236.Controller.SelectErase
