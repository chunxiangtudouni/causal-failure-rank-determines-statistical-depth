module

public import Paid.PDLower_CalibrationCompute_Frame_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem flatMap_block_fetch {α β : Type*} (code : α → List β) (before : List α) (current : α)
    (after : List α) (offset : ℕ) (inside : offset < (code current).length) :
    ((before++current::after).flatMap code)[((before.map (fun entry => (code entry).length)).sum)+offset]? =
      (code current)[offset]? := by
  rw [List.flatMap_append,List.flatMap_cons,← List.length_flatMap]
  rw [List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
  exact List.getElem?_append_left inside

theorem labels_split (label : Label) :
    labels = labels.take (labels.idxOf label) ++ label :: labels.drop (labels.idxOf label+1) := by
  have inside : labels.idxOf label < labels.length := List.idxOf_lt_length_iff.mpr (labels_complete label)
  have identity := List.set_getElem_self (as := labels) (i := labels.idxOf label) inside
  rw [List.getElem_idxOf inside] at identity
  rw [List.set_eq_take_append_cons_drop,ite_eq_left inside] at identity
  exact identity.symm

theorem kernel_block_fetch (origin : ℕ) (label : Label) (offset : ℕ)
    (inside : offset < (compiledBlock origin label).length) :
    (PDMenu.ComputeFrame.locatedBlock origin (kernel origin))[labelAddress origin label+offset]? =
      (compiledBlock origin label)[offset]? := by
  simp only [labelAddress,Nat.add_assoc]
  rw [PDMenu.ComputeFrame.locatedBlock_fetch]
  simp only [kernel,List.getElem?_toArray]
  have raw := flatMap_block_fetch (compiledBlock origin) (labels.take (labels.idxOf label)) label
    (labels.drop (labels.idxOf label+1)) offset inside
  simpa only [← labels_split label,compiledBlock_length] using raw

theorem kernel_body_fetch (origin : ℕ) (label : Label) (offset : ℕ)
    (inside : offset < (basicBlock label).body.length) :
    (PDMenu.ComputeFrame.locatedBlock origin (kernel origin))[labelAddress origin label+offset]? =
      (basicBlock label).body[offset]? := by
  rw [kernel_block_fetch origin label offset (by rw [compiledBlock_length,blockLength]; omega)]
  exact List.getElem?_append_left inside

theorem kernel_control_fetch (origin : ℕ) (label : Label) :
    (PDMenu.ComputeFrame.locatedBlock origin (kernel origin))[labelAddress origin label+(basicBlock label).body.length]? =
      some (controlInstruction origin (basicBlock label).control) := by
  rw [kernel_block_fetch origin label _ (by rw [compiledBlock_length,blockLength]; omega)]
  simp only [compiledBlock,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero]

theorem kernel_control_step (origin : ℕ) (label : Label) (input : List Cell) (state : State)
    (position : state.pc = labelAddress origin label+(basicBlock label).body.length) :
    step (PDMenu.ComputeFrame.locatedBlock origin (kernel origin)) input state =
      (controlInstruction origin (basicBlock label).control).execute input state := by
  unfold step
  rw [position,kernel_control_fetch]
  rfl

end PDLower.CalibrationCompute
