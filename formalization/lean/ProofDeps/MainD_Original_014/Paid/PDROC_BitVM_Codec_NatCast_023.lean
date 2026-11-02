module

public import Paid.PDROC_BitVM_Codec_FieldOps_016
public import Paid.PDROC_BitVM_Kernel_NatMarshal_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.NatCast

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation

abbrev Stack := FieldOps.Stack
abbrev Alphabet := FieldOps.Alphabet
abbrev Label := FieldOps.Label
abbrev WriterStore := FieldOps.WriterStore
abbrev Store := FieldOps.Store
abbrev State := FieldOps.State
abbrev Statement := FieldOps.Statement

def control := FieldOps.control
def marshalLabels := FieldOps.marshalLabels
def writerLabels := FieldOps.writerLabels
def assemblerLabels := FieldOps.readerLabels

def tempWriter := NatWriter.Global.machine 25 (by decide) (by decide)

/-- This literal is fixed before every source Natural. It is produced by
real target clearing and actual constant Bool writes, not supplied as data. -/
def one : List Bool := encodeCellBits (.natural 1)

def literalEmbedding : Fin 3 ↪ Stack := RatMarshal.headerEmbedding 1

/-- Original natToRat implementation: actual source Nat tag/copy/restore,
canonical private Nat writeback, real denominator1 literal producer, then
the same actual Rat Cell assembler. Source is read before clearing target,
so target=source is allowed. Work0/24 and used temps25/26 are really cleared.
No transition evaluates the mathematical Nat cast or a Rat normalizer. -/
def program (target source : Register) : Label → Statement
  | .inl index =>
      if index = 0 then .load (fun _ => FieldOps.clearedStore) (.goto (fun _ => control 1))
      else if index = 1 then FieldOps.clearStatement 0 (control 1) (control 2)
      else if index = 2 then FieldOps.clearStatement 24 (control 2) (marshalLabels 0)
      else if index = 3 then StoreIso.statement FieldOps.clearIso
        (Inline.statement (τ := Bool × FieldOps.WriterStore) (fun _ : Unit => control 3) (assemblerLabels 0)
          (Lift.statement literalEmbedding (PDROC.BitVM.Kernel.RegisterMove.literalProgram one ())))
      else if index = 4 then FieldOps.clearStatement 25 (control 4) (control 5)
      else if index = 5 then FieldOps.clearStatement 26 (control 5) (control 6)
      else .load (fun _ => FieldOps.clearedStore) .halt
  | .inr (.inl label) =>
      Inline.statement assemblerLabels (control 4) (RatAssembler.program target 0 1 label)
  | .inr (.inr (.inl label)) =>
      StoreIso.statement (Equiv.prodComm _ _)
        (Inline.statement marshalLabels (writerLabels 0)
          (PDROC.BitVM.Kernel.NatMarshalGlobal.machine source label))
  | .inr (.inr (.inr label)) =>
      StoreIso.statement (Equiv.prodComm _ _)
        (Inline.statement writerLabels (control 3) (tempWriter label))

def before (contents : Stack → List Bool) (saved : Store) : State := ⟨some (control 0), saved, contents⟩

theorem marshal_agrees (target source : Register) (label : PDROC.BitVM.Kernel.NatMarshal.Label) :
    program target source (marshalLabels label) = StoreIso.statement (Equiv.prodComm _ _)
      (Inline.statement marshalLabels (writerLabels 0) (PDROC.BitVM.Kernel.NatMarshalGlobal.machine source label)) := rfl

theorem writer_agrees (target source : Register) (label : NatWriter.Label) :
    program target source (writerLabels label) = StoreIso.statement (Equiv.prodComm _ _)
      (Inline.statement writerLabels (control 3) (tempWriter label)) := rfl

theorem literal_agrees (target source : Register) (label : Unit) :
    program target source (control 3) = StoreIso.statement FieldOps.clearIso
      (Inline.statement (τ := Bool × FieldOps.WriterStore) (fun _ : Unit => control 3) (assemblerLabels 0)
        (Lift.machine literalEmbedding (PDROC.BitVM.Kernel.RegisterMove.literalProgram one) label)) := by
  cases label
  rfl

theorem assembler_agrees (target source : Register) (label : RatAssembler.Label) :
    program target source (assemblerLabels label) =
      Inline.statement assemblerLabels (control 4) (RatAssembler.program target 0 1 label) := rfl

theorem reset_step (target source : Register) (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program target source) (before contents saved) =
      some (⟨some (control 1), FieldOps.clearedStore, contents⟩ : State) := rfl

theorem finish_step (target source : Register) (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program target source) (⟨some (control 6), saved, contents⟩ : State) =
      some (⟨none, FieldOps.clearedStore, contents⟩ : State) := rfl

theorem supports (target source : Register) : TM2.Supports (program target source) Finset.univ := by
  have every : ∀ code : Statement, TM2.SupportsStmt Finset.univ code := by
    intro code
    induction code with
    | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
    | branch _ _ _ yes no => exact ⟨yes, no⟩
    | goto _ => exact fun _ => Finset.mem_univ _
    | halt => trivial
  exact ⟨Finset.mem_univ _, fun label _ => every (program target source label)⟩

end PDROC.BitVM.Codec.NatCast
