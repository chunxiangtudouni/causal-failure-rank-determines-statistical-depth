module

public import RootB236_Controller_EraseSem_Core_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace RootB236.Controller.EraseSem.Public

variable {q : Nat}

/-- Canonical real-stack shape and exact semantic result of its one-cell
FALSE overwrite. This is a representation theorem, not free computation. -/
theorem split_mask (remaining : Finset (Fin q)) (tool : Fin q) :
    ∃ front suffix,
      mask remaining=front++decide (tool∈remaining)::suffix ∧
      front.length=tool.val ∧ front.length+1+suffix.length=q ∧
      mask (remaining.erase tool)=front++false::suffix ∧
      (front++false::suffix).length=q := by
  refine ⟨(mask remaining).take tool.val,(mask remaining).drop (tool.val+1),
    mask_decomposition remaining tool,prefix_length remaining tool,?_,
    mask_erase_take_drop remaining tool,?_⟩
  · have length := congrArg List.length (mask_decomposition remaining tool)
    simp only [mask_length,List.length_append,List.length_cons] at length
    omega
  · rw [←mask_erase_take_drop remaining tool,mask_length]

/-- This consumes any actual physical decomposition and physical result,
so a verified TM2 leaf can be attached without inspecting its implementation. -/
theorem physical_result (remaining : Finset (Fin q)) (tool : Fin q)
    (front suffix : List Bool) (head : Bool) (after : List Bool)
    (represented : mask remaining=front++head::suffix)
    (position : front.length=tool.val) (physical : after=front++false::suffix) :
    after=mask (remaining.erase tool) ∧ after.length=q := by
  have semantic := physical.trans (erase_of_decomposition remaining tool front suffix head represented position)
  exact ⟨semantic,by rw [semantic,mask_length]⟩

theorem physical_result_iff (remaining : Finset (Fin q)) (tool : Fin q)
    (front suffix : List Bool) (head : Bool) (after : List Bool)
    (represented : mask remaining=front++head::suffix) (position : front.length=tool.val) :
    after=front++false::suffix ↔ after=mask (remaining.erase tool) := by
  rw [erase_of_decomposition remaining tool front suffix head represented position]

theorem no_membership_qualification (remaining : Finset (Fin q)) (tool : Fin q) :
    (mask (remaining.erase tool)).length=q ∧
    mask (remaining.erase tool)=
      (mask remaining).take tool.val ++ false::(mask remaining).drop (tool.val+1) :=
  ⟨mask_length _,mask_erase_take_drop remaining tool⟩

end RootB236.Controller.EraseSem.Public
