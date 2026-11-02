module

public import Paid.PDROC_BitVM_Codec_RatMarshal_008
public import Paid.PDROC_BitVM_Native_StoreTrace_013

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.RatAssembler

open Turing PDROC.BitVM.Native

abbrev Stack := RatMarshal.Stack
abbrev Alphabet := RatMarshal.Alphabet
abbrev Label := RatMarshal.Label
abbrev Store := RatMarshal.Store
abbrev State := RatMarshal.State
abbrev Statement := RatMarshal.Statement
abbrev Register := RatMarshal.Register

/-- This is only an isomorphism of fixed FINITE stores. The Unit carries
no data; the real sign stays in the caller's separate Bool component. -/
def natStoreIso : PDROC.BitVM.Kernel.NatMarshal.Store ≃ Option Bool where
  toFun := Prod.fst
  invFun := fun saved => (saved, ())
  left_inv := by intro saved; rcases saved with ⟨saved, marker⟩; cases marker; rfl
  right_inv := by intro saved; rfl

def natProgram : PDROC.BitVM.Kernel.NatMarshal.Label →
    TM2.Stmt (fun _ : Fin 3 => Bool) PDROC.BitVM.Kernel.NatMarshal.Label (Option Bool) :=
  StoreIso.machine natStoreIso PDROC.BitVM.Kernel.NatMarshal.program

/-- Temp, original target, real native LEFT; these roles are distinct by
the fixed global bank layout, before all arithmetic values and widths. -/
def embedding (temp : Fin 7) (target : Register) : Fin 3 ↪ Stack where
  toFun := fun role => if role = 0 then RatMarshal.tempSlot temp
    else if role = 1 then PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target else 24
  inj' := by
    intro left right same
    have values := congrArg Fin.val same
    have tempBound := RatMarshal.tempSlot_bounds temp
    have targetBounds := PDROC.BitVM.Kernel.RegisterGlobal.registerSlot_bounds target
    fin_cases left <;> fin_cases right <;> simp at values ⊢ <;> omega

def denominatorLabels (label : PDROC.BitVM.Kernel.NatMarshal.Label) : Label :=
  ⟨2 + label.val, by omega⟩

def numeratorLabels (label : PDROC.BitVM.Kernel.NatMarshal.Label) : Label :=
  ⟨7 + label.val, by omega⟩

/-- Actual normalization is the caller's arithmetic computation. This
writer copies its two already-canonical Nat Cells and finite sign. It
does not decode or normalize a Rat in host control. Native-right0 is
outside every call and is retained, even when it contains old bytes. -/
def program (target : Register) (num den : Fin 7) (label : Label) : Statement :=
  if label = 0 then Inline.statement (fun _ : Unit => 0) 1
    (Lift.statement (embedding den target) (NatWriter.clearProgram 2 ()))
  else if label = 1 then Inline.statement (fun _ : Unit => 1) 2
    (Lift.statement (embedding den target) (NatWriter.clearProgram 1 ()))
  else if small : label.val < 7 then Inline.statement denominatorLabels 7
    (Lift.statement (embedding den target) (natProgram ⟨label.val - 2, by omega⟩))
  else if small : label.val < 12 then Inline.statement numeratorLabels 12
    (Lift.statement (embedding num target) (natProgram ⟨label.val - 7, by omega⟩))
  else if label = 12 then
    .push (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) (fun saved => saved.2)
      (.push (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) (fun _ => true) .halt)
  else .halt

theorem clear_left_agrees (target : Register) (num den : Fin 7) (label : Unit) :
    program target num den 0 = Inline.statement (fun _ : Unit => 0) 1
      (Lift.machine (embedding den target) (NatWriter.clearProgram 2) label) := by
  cases label
  rfl

theorem clear_target_agrees (target : Register) (num den : Fin 7) (label : Unit) :
    program target num den 1 = Inline.statement (fun _ : Unit => 1) 2
      (Lift.machine (embedding den target) (NatWriter.clearProgram 1) label) := by
  cases label
  rfl

theorem denominator_agrees (target : Register) (num den : Fin 7)
    (label : PDROC.BitVM.Kernel.NatMarshal.Label) :
    program target num den (denominatorLabels label) = Inline.statement denominatorLabels 7
      (Lift.machine (embedding den target) natProgram label) := by
  fin_cases label <;> rfl

theorem numerator_agrees (target : Register) (num den : Fin 7)
    (label : PDROC.BitVM.Kernel.NatMarshal.Label) :
    program target num den (numeratorLabels label) = Inline.statement numeratorLabels 12
      (Lift.machine (embedding num target) natProgram label) := by
  fin_cases label <;> rfl

theorem supports (target : Register) (num den : Fin 7) :
    TM2.Supports (program target num den) Finset.univ := by
  have every : ∀ code : Statement, TM2.SupportsStmt Finset.univ code := by
    intro code
    induction code with
    | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
    | branch _ _ _ yes no => exact ⟨yes, no⟩
    | goto _ => exact fun _ => Finset.mem_univ _
    | halt => trivial
  exact ⟨Finset.mem_univ _, fun label _ => every (program target num den label)⟩

end PDROC.BitVM.Codec.RatAssembler
