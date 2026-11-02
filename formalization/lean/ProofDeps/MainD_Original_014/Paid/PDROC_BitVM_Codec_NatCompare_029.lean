module

public import Paid.PDROC_BitVM_Codec_NatCompare_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Codec.NatCompare

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Codec.FieldOps (Path)

abbrev BranchStore := PDROC.BitVM.Kernel.Branch.Store
abbrev BranchTail := Option Bool × Option Bool × Option Bool × Option Bool
abbrev Store := BranchStore × (CoreStore × Bool)
abbrev Label := Fin 10 ⊕ ((Bool × CoreLabel) ⊕ NatWriter.Label)
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def control (index : Fin 10) : Label := .inl index
def coreLabels (direction : Bool) (label : CoreLabel) : Label := .inr (.inl (direction, label))
def writerLabels (label : NatWriter.Label) : Label := .inr (.inr label)
def coreInitial : CoreStore := (coreBefore (fun _ => []) none).var
def clearedStore : Store := ((none, none, none, none, none), (coreInitial, false))

def orderedLeft (direction : Bool) (left right : Register) : Register := if direction then right else left
def orderedRight (direction : Bool) (left right : Register) : Register := if direction then left else right
def tempSlot (direction : Bool) : Stack := if direction then 26 else 25
def coreFinish (direction : Bool) : Label := if direction then control 5 else control 3

theorem temp_not_right (direction : Bool) : tempSlot direction ≠ 0 := by cases direction <;> decide
theorem temp_not_left (direction : Bool) : tempSlot direction ≠ 24 := by cases direction <;> decide

def coreMachine (direction : Bool) (left right : Register) :=
  coreProgram (tempSlot direction) (temp_not_right direction) (temp_not_left direction)
    (orderedLeft direction left right) (orderedRight direction left right)

def coreIso : (CoreStore × (BranchStore × Bool)) ≃ Store where
  toFun := fun data => (data.2.1, (data.1, data.2.2))
  invFun := fun data => (data.2.1, (data.1, data.2.2))
  left_inv := by intro data; rfl
  right_inv := by intro data; rfl

def writerIso : (NatWriter.Store × (BranchStore × (ComputeStore × Bool))) ≃ Store where
  toFun := fun data => (data.2.1, ((data.2.2.1, data.1), data.2.2.2))
  invFun := fun data => (data.2.1.2, (data.1, (data.2.1.1, data.2.2)))
  left_inv := by intro data; rfl
  right_inv := by intro data; rfl

def clearIso : (Option Bool × (BranchTail × (CoreStore × Bool))) ≃ Store :=
  (Equiv.prodAssoc _ _ _).symm

def clearStatement (slot : Stack) (start finish : Label) : Statement :=
  StoreIso.statement clearIso
    (Inline.statement (τ := BranchTail × (CoreStore × Bool)) (fun _ : Unit => start) finish
      (PDROC.BitVM.Kernel.Clear.program slot ()))

def combine (comparison : Comparison) (ab ba : Bool) : Bool := match comparison with
  | .equal => ab && ba
  | .less => ab && !ba
  | .lessEqual => ab

def resultFlag (comparison : Comparison) (saved : Store) : Bool :=
  combine comparison saved.2.2 (!PDROC.BitVM.Kernel.Branch.zeroFlag saved.1)

def writerMachine (target : Register) := NatWriter.Global.machine (registerSlot target)
  (RatMarshal.source_not_right target) (RatMarshal.register_not_left target)

/-- Both LE results are actually written as Cells and read by genuine
five-byte peek/restore. The Bool composition is finite control. Only after
both original-source reads is the original target actually overwritten. -/
def program (comparison : Comparison) (target left right : Register) : Label → Statement
  | .inl index =>
    if index = 0 then .load (fun _ => clearedStore) (.goto (fun _ => control 1))
    else if index = 1 then clearStatement 0 (control 1) (control 2)
    else if index = 2 then clearStatement 24 (control 2) (coreLabels false (.inl 0))
    else if index = 3 then Inline.statement (τ := CoreStore × Bool) (fun _ : Unit => control 3) (control 4)
      (PDROC.BitVM.Kernel.Branch.program 25 ())
    else if index = 4 then .load (fun saved => (saved.1,
      (coreInitial, !PDROC.BitVM.Kernel.Branch.zeroFlag saved.1))) (.goto (fun _ => coreLabels true (.inl 0)))
    else if index = 5 then Inline.statement (τ := CoreStore × Bool) (fun _ : Unit => control 5) (control 6)
      (PDROC.BitVM.Kernel.Branch.program 26 ())
    else if index = 6 then .push 0 (resultFlag comparison)
      (.push 0 (fun _ => false) (.push 0 (fun _ => true) (.goto (fun _ => writerLabels 0))))
    else if index = 7 then clearStatement 25 (control 7) (control 8)
    else if index = 8 then clearStatement 26 (control 8) (control 9)
    else .load (fun _ => clearedStore) .halt
  | .inr (.inl (direction, label)) => StoreIso.statement coreIso
      (Inline.statement (coreLabels direction) (coreFinish direction) (coreMachine direction left right label))
  | .inr (.inr label) => StoreIso.statement writerIso
      (Inline.statement writerLabels (control 7) (writerMachine target label))

def before (contents : Stack → List Bool) (saved : Store) : State := ⟨some (control 0), saved, contents⟩

theorem supports (comparison : Comparison) (target left right : Register) :
    TM2.Supports (program comparison target left right) Finset.univ := by
  have every : ∀ code : Statement, TM2.SupportsStmt Finset.univ code := by
    intro code
    induction code with
    | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
    | branch _ _ _ yes no => exact ⟨yes, no⟩
    | goto _ => exact fun _ => Finset.mem_univ _
    | halt => trivial
  exact ⟨Finset.mem_univ _, fun label _ => every (program comparison target left right label)⟩

theorem reset_step (comparison : Comparison) (target left right : Register)
    (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program comparison target left right) (before contents saved) =
      some (⟨some (control 1), clearedStore, contents⟩ : State) := rfl

theorem finish_step (comparison : Comparison) (target left right : Register)
    (contents : Stack → List Bool) (saved : Store) :
    TM2.step (program comparison target left right) (⟨some (control 9), saved, contents⟩ : State) =
      some (⟨none, clearedStore, contents⟩ : State) := rfl

theorem combine_correct (comparison : Comparison) (a b : ℕ) :
    combine comparison (decide (a ≤ b)) (decide (b ≤ a)) = comparison.nat a b := by
  apply Bool.eq_iff_iff.mpr
  cases comparison <;> by_cases ab : a ≤ b <;> by_cases ba : b ≤ a
  all_goals simp_all [combine, Comparison.nat]
  all_goals omega

def clearSlot (stage : Fin 4) : Stack := ![0, 24, 25, 26] stage
def clearStart (stage : Fin 4) : Label := ![control 1, control 2, control 7, control 8] stage
def clearFinish (stage : Fin 4) : Label := ![control 2, coreLabels false (.inl 0), control 8, control 9] stage

theorem clear_agrees (comparison : Comparison) (target left right : Register) (stage : Fin 4) (label : Unit) :
    program comparison target left right (clearStart stage) = StoreIso.statement clearIso
      (Inline.statement (τ := BranchTail × (CoreStore × Bool)) (fun _ : Unit => clearStart stage)
        (clearFinish stage) (PDROC.BitVM.Kernel.Clear.program (clearSlot stage) label)) := by
  cases label
  fin_cases stage <;> rfl

def clearCfg (stage : Fin 4) (extra : BranchTail × (CoreStore × Bool))
    (source : PDROC.BitVM.Kernel.Clear.State) : State :=
  StoreIso.cfg clearIso (Inline.cfg (fun _ : Unit => clearStart stage) (clearFinish stage) extra source)

theorem clear_call (comparison : Comparison) (target left right : Register) (stage : Fin 4)
    (contents : Stack → List Bool) (saved : Store) :
    ∃ path : Path (program comparison target left right)
      (⟨some (clearStart stage), saved, contents⟩ : State)
      (⟨some (clearFinish stage), ((none, saved.1.2), saved.2),
        Function.update contents (clearSlot stage) []⟩ : State),
      path.states.length = (contents (clearSlot stage)).length + 2 := by
  obtain ⟨run, head, chain, last, _halt, length, _frame⟩ :=
    PDROC.BitVM.Kernel.Clear.runs (clearSlot stage) contents saved.1.1
  let localPath : Path (PDROC.BitVM.Kernel.Clear.program (clearSlot stage))
      (⟨some (), saved.1.1, contents⟩ : PDROC.BitVM.Kernel.Clear.State)
      (⟨none, none, Function.update contents (clearSlot stage) []⟩ : PDROC.BitVM.Kernel.Clear.State) :=
    ⟨run, head, chain, last⟩
  let transform := clearCfg stage (saved.1.2, saved.2)
  have edge : ∀ a b, TM2.step (PDROC.BitVM.Kernel.Clear.program (clearSlot stage)) a = some b →
      TM2.step (program comparison target left right) (transform a) = some (transform b) := by
    intro a b actual
    exact FieldOps.iso_inline_edge clearIso (fun _ : Unit => clearStart stage) (clearFinish stage)
      (saved.1.2, saved.2) (PDROC.BitVM.Kernel.Clear.program (clearSlot stage))
      (program comparison target left right) (clear_agrees comparison target left right stage) a b actual
  exact ⟨localPath.transport transform edge, (localPath.transport_length transform edge).trans length⟩

end PDROC.BitVM.Codec.NatCompare
