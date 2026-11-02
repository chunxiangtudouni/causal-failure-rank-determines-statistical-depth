module

public import Paid.PDROC_BitVM_Codec_RatAssembler_014

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.FieldOps

open Turing PDROC.BitVM.Native
open PaperProofs.Paid.Computation

inductive Kind where
  | numeratorAbs | denominator | negative
  deriving Inhabited, DecidableEq

instance : Fintype Kind where
  elems := {.numeratorAbs, .denominator, .negative}
  complete := by intro kind; cases kind <;> decide

def Kind.value : Kind → ℚ → ℕ
  | .numeratorAbs, value => value.num.natAbs
  | .denominator, value => value.den
  | .negative, value => if value < 0 then 1 else 0

def Kind.instruction (kind : Kind) (target source : Register) : Instruction :=
  match kind with
  | .numeratorAbs => .numeratorAbs target source
  | .denominator => .denominator target source
  | .negative => .negative target source

abbrev Stack := RatMarshal.Stack
abbrev Alphabet := RatMarshal.Alphabet
abbrev WriterStore := NatWriter.Store
abbrev Store := RatMarshal.Store × WriterStore
abbrev Label := Fin 7 ⊕ (RatMarshal.Label ⊕ (PDROC.BitVM.Kernel.NatMarshal.Label ⊕ NatWriter.Label))
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def control (index : Fin 7) : Label := .inl index
def readerLabels (label : RatMarshal.Label) : Label := .inr (.inl label)
def marshalLabels (label : PDROC.BitVM.Kernel.NatMarshal.Label) : Label := .inr (.inr (.inl label))
def writerLabels (label : NatWriter.Label) : Label := .inr (.inr (.inr label))

def clearedStore : Store := ((none, false), (none, ()))

def clearIso : (Option Bool × (Bool × WriterStore)) ≃ Store :=
  (Equiv.prodAssoc _ _ _).symm

def clearStatement (slot : Stack) (start finish : Label) : Statement :=
  StoreIso.statement clearIso
    (Inline.statement (τ := Bool × WriterStore) (fun _ : Unit => start) finish
      (PDROC.BitVM.Kernel.Clear.program slot ()))

def selectedTemp : Kind → Fin 7
  | .numeratorAbs => 0
  | .denominator => 1
  | .negative => 0

/-- The selected temporary, native-right, native LEFT. The field is an
actual full Nat Cell produced by the same concrete Rat reader. -/
def fieldEmbedding (kind : Kind) : Fin 3 ↪ Stack where
  toFun := fun role => if role = 0 then RatMarshal.tempSlot (selectedTemp kind)
    else if role = 1 then 0 else 24
  inj' := by
    intro left right equal
    have values := congrArg Fin.val equal
    have bound := RatMarshal.tempSlot_bounds (selectedTemp kind)
    fin_cases left <;> fin_cases right <;> simp at values ⊢ <;> omega

def writerMachine (target : Register) := NatWriter.Global.machine
  (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)
  (RatMarshal.source_not_right target) (RatMarshal.register_not_left target)

/-- Three original rational field operations. Every control/store type
is fixed before values and widths. Both work buffers are really cleared
before reading; both used field temporaries are really cleared on exit.
The negative case writes [true,false,actualReadSign], a genuine bare Nat
0/1 word, before calling the SAME canonical Nat writer as the other cases.
Kind.value and Instruction.execute are specifications, never transitions. -/
def program (kind : Kind) (target source : Register) : Label → Statement
  | .inl index =>
      if index = 0 then .load (fun _ => clearedStore) (.goto (fun _ => control 1))
      else if index = 1 then clearStatement 0 (control 1) (control 2)
      else if index = 2 then clearStatement 24 (control 2) (readerLabels 0)
      else if index = 3 then match kind with
        | .numeratorAbs | .denominator => .goto (fun _ => marshalLabels 0)
        | .negative => .push 0 (fun saved => saved.1.2)
            (.push 0 (fun _ => false) (.push 0 (fun _ => true) (.goto (fun _ => writerLabels 0))))
      else if index = 4 then clearStatement 25 (control 4) (control 5)
      else if index = 5 then clearStatement 26 (control 5) (control 6)
      else .load (fun _ => clearedStore) .halt
  | .inr (.inl label) =>
      Inline.statement readerLabels (control 3) (RatMarshal.program source 0 1 (by decide) label)
  | .inr (.inr (.inl label)) =>
      StoreIso.statement (Equiv.prodComm _ _)
        (Inline.statement marshalLabels (writerLabels 0)
          (Lift.statement (fieldEmbedding kind) (PDROC.BitVM.Kernel.NatMarshal.program label)))
  | .inr (.inr (.inr label)) =>
      StoreIso.statement (Equiv.prodComm _ _)
        (Inline.statement writerLabels (control 4) (writerMachine target label))

def before (contents : Stack → List Bool) (saved : Store) : State := ⟨some (control 0), saved, contents⟩

theorem reader_agrees (kind : Kind) (target source : Register) (label : RatMarshal.Label) :
    program kind target source (readerLabels label) =
      Inline.statement readerLabels (control 3) (RatMarshal.program source 0 1 (by decide) label) := rfl

theorem writer_agrees (kind : Kind) (target source : Register) (label : NatWriter.Label) :
    program kind target source (writerLabels label) = StoreIso.statement (Equiv.prodComm _ _)
      (Inline.statement writerLabels (control 4) (writerMachine target label)) := rfl

theorem marshal_agrees (kind : Kind) (target source : Register)
    (label : PDROC.BitVM.Kernel.NatMarshal.Label) :
    program kind target source (marshalLabels label) = StoreIso.statement (Equiv.prodComm _ _)
      (Inline.statement marshalLabels (writerLabels 0)
        (Lift.statement (fieldEmbedding kind) (PDROC.BitVM.Kernel.NatMarshal.program label))) := rfl

theorem supports (kind : Kind) (target source : Register) :
    TM2.Supports (program kind target source) Finset.univ := by
  have every : ∀ code : Statement, TM2.SupportsStmt Finset.univ code := by
    intro code
    induction code with
    | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
    | branch _ _ _ yes no => exact ⟨yes, no⟩
    | goto _ => exact fun _ => Finset.mem_univ _
    | halt => trivial
  exact ⟨Finset.mem_univ _, fun label _ => every (program kind target source label)⟩

end PDROC.BitVM.Codec.FieldOps
