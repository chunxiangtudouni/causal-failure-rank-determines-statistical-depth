module

public import Paid.PDROC_BitVM_Kernel_ResultCell_032
public import Paid.PDROC_BitVM_Kernel_Clear_006
public import Paid.PDROC_BitVM_Native_StoreTrace_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawWrite

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev Label := Fin 5 ⊕ (ResultCell.Label ⊕ Unit)
abbrev Store := Option Bool × ResultCell.Store
abbrev State := TM2.Cfg Alphabet Label Store

def clearLabel (phase : Fin 5) : Label := .inl phase
def cellLabel (label : ResultCell.Label) : Label := .inr (.inl label)
def doneLabel : Label := .inr (.inr ())
def cellStart : Label := cellLabel PDROC.BitVM.Log.BankField.startLabel

/-- Parser ticks/native-left, capture and actual old destination are
really erased before the Cell scan. Residual input/padding and archive
are really erased afterwards. Other original registers and banks carry. -/
def clearRole (target : Register) (phase : Fin 5) : Stack :=
  if phase=0 then 24 else if phase=1 then 29 else if phase=2 then registerSlot target
  else if phase=3 then 0 else 25

def nextLabel (phase : Fin 5) : Label :=
  if h : phase.val<2 then clearLabel ⟨phase.val+1,by omega⟩
  else if phase=2 then cellStart else if phase=3 then clearLabel 4 else doneLabel

/-- Fixed finite code. Only real popped bits occur in the finite store;
there is no decoded Cell, rational value, length or input-dependent role. -/
def program (target : Register) : Label → TM2.Stmt Alphabet Label Store
  | .inl phase => Inline.statement (fun _ : Unit=>clearLabel phase) (nextLabel phase)
      (Clear.program (clearRole target phase) ())
  | .inr (.inl label) => StoreIso.statement (Equiv.prodComm _ _)
      (Inline.statement cellLabel (clearLabel 3) (ResultCell.program target label))
  | .inr (.inr _) => .halt

def before (contents : Stack → List Bool) (saved : ResultCell.Store) : State :=
  ⟨some (clearLabel 0),(none,saved),contents⟩

theorem clear_agrees (target : Register) (phase : Fin 5) : ∀ label : Unit,
    program target (clearLabel phase)=
      Inline.statement (fun _ : Unit=>clearLabel phase) (nextLabel phase)
        (Clear.program (clearRole target phase) label) := by
  intro label
  cases label
  rfl

theorem supports (target : Register) : TM2.Supports (program target) (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with phase | (cell | marker)
    · exact Inline.supports_statement (fun _ : Unit=>clearLabel phase) (nextLabel phase) Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (Clear.program (clearRole target phase) ())
        ((Clear.supports (clearRole target phase)).2 () (Finset.mem_univ _))
    · exact StoreIso.supports_statement (Equiv.prodComm _ _) Finset.univ _
        (Inline.supports_statement cellLabel (clearLabel 3) Finset.univ Finset.univ
          (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (ResultCell.program target cell)
          ((ResultCell.supports target).2 cell (Finset.mem_univ _)))
    · trivial

end PDROC.BitVM.Kernel.RawWrite
