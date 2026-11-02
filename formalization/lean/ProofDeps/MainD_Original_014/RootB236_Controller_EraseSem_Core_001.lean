module

public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.Finset.Erase

/-! A mathematical representation bridge, not an executable mask producer.
The physical component receives real bits and an actual unary position;
these lemmas identify its single FALSE overwrite with original Finset.erase.
All finite positions, including FALSE heads, are covered without membership
or positive-q qualifications. A tool : Fin 0 cannot be supplied. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace RootB236.Controller.EraseSem

def mask {q : Nat} (remaining : Finset (Fin q)) : List Bool :=
  List.ofFn (fun tool : Fin q => decide (tool∈remaining))

variable {q : Nat}

@[simp] theorem mask_length (remaining : Finset (Fin q)) : (mask remaining).length=q := by
  simp [mask]

@[simp] theorem mask_at (remaining : Finset (Fin q)) (tool : Fin q) :
    (mask remaining)[tool.val]'(by simpa only [mask_length] using tool.isLt)=decide (tool∈remaining) := by
  simp [mask]

/-- Reuse the standard List.set representation of one physical overwrite. -/
theorem mask_erase_set (remaining : Finset (Fin q)) (tool : Fin q) :
    mask (remaining.erase tool)=(mask remaining).set tool.val false := by
  apply List.ext_getElem (by simp)
  intro index _left _right
  by_cases same : tool.val=index
  · simp [mask,Finset.mem_erase,Fin.ext_iff,same]
  · simp [mask,Finset.mem_erase,Fin.ext_iff,same,Ne.symm same]

theorem mask_erase_take_drop (remaining : Finset (Fin q)) (tool : Fin q) :
    mask (remaining.erase tool)=
      (mask remaining).take tool.val ++ false::(mask remaining).drop (tool.val+1) := by
  rw [mask_erase_set,List.set_eq_take_append_cons_drop]
  exact ite_eq_left (by simpa only [mask_length] using tool.isLt)

theorem mask_decomposition (remaining : Finset (Fin q)) (tool : Fin q) :
    mask remaining=(mask remaining).take tool.val ++
      decide (tool∈remaining)::(mask remaining).drop (tool.val+1) := by
  have inside : tool.val<(mask remaining).length := by simpa only [mask_length] using tool.isLt
  calc
    mask remaining=(mask remaining).take tool.val ++ (mask remaining).drop tool.val :=
      (List.take_append_drop _ _).symm
    _=(mask remaining).take tool.val ++ decide (tool∈remaining)::(mask remaining).drop (tool.val+1) := by
      rw [List.drop_eq_getElem_cons inside,mask_at]

theorem prefix_length (remaining : Finset (Fin q)) (tool : Fin q) :
    ((mask remaining).take tool.val).length=tool.val := by
  rw [List.length_take,mask_length,Nat.min_eq_left (Nat.le_of_lt tool.isLt)]

theorem suffix_length (remaining : Finset (Fin q)) (tool : Fin q) :
    ((mask remaining).drop (tool.val+1)).length=q-(tool.val+1) := by
  rw [List.length_drop,mask_length]

theorem erase_same_length (remaining : Finset (Fin q)) (tool : Fin q) :
    (mask (remaining.erase tool)).length=(mask remaining).length := by simp

/-- An arbitrary physical front/head/suffix decomposition is enough.
The head need not be TRUE, and no assumption tool∈remaining is added. -/
theorem erase_of_decomposition (remaining : Finset (Fin q)) (tool : Fin q)
    (front suffix : List Bool) (head : Bool)
    (represented : mask remaining=front++head::suffix) (position : front.length=tool.val) :
    front++false::suffix=mask (remaining.erase tool) := by
  rw [mask_erase_set,represented,←position]
  simp

theorem head_of_decomposition (remaining : Finset (Fin q)) (tool : Fin q)
    (front suffix : List Bool) (head : Bool)
    (represented : mask remaining=front++head::suffix) (position : front.length=tool.val) :
    head=decide (tool∈remaining) := by
  have lookup : (mask remaining)[tool.val]?=some (decide (tool∈remaining)) := by
    simp [mask,tool.isLt]
  rw [represented,←position,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,
    List.getElem?_cons_zero] at lookup
  exact Option.some.inj lookup

end RootB236.Controller.EraseSem
