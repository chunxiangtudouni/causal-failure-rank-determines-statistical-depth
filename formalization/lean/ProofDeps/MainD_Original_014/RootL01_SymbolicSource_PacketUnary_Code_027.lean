module

public import RootL01_SymbolicSource_Unary_Public_024
public import Structure.L01_3_5_TABLE_NatSerializer_Collect_020

/-! The packet is actually collected/restored by frozen L01 H007 before
the new finite Horner source runs.  Neither the value nor its MSB payload
is loaded into finite control. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.PacketUnary

open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool

abbrev Collector := L01_3_5_TABLE_NatSerializer019.Label
abbrev Bank := Unary.Bank
abbrev Store (C : Type*) := RatInput.Memory (C×Unary.Registers)

inductive Label where
  | collect : Collector → Label
  | convert : Unary.Label → Label
  | done
  deriving DecidableEq

instance : Fintype Label where
  elems := (Finset.univ.image Label.collect) ∪ (Finset.univ.image Label.convert) ∪ {.done}
  complete := by intro point; cases point <;> simp

instance : Inhabited Label := ⟨.collect 0⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def convertIso (C : Type*) : Unary.Store (C×RatInput.Store) ≃ Store C where
  toFun value := ((value.1.1,value.2),value.1.2)
  invFun value := ((value.1.1,value.2),value.1.2)
  left_inv := by intro value; rcases value with ⟨⟨context,rat⟩,registers⟩; rfl
  right_inv := by intro value; rcases value with ⟨⟨context,registers⟩,rat⟩; rfl

def collectLabel (point : Collector) : Label := if point=4 then .convert .read else .collect point
def convertLabel (point : Unary.Label) : Label := if point=.done then .done else .convert point

def program (caller : Statement C) : Label → Statement C
  | .collect point => LabelMap.statement collectLabel (L01_3_5_TABLE_NatSerializer019.collectProgram point)
  | .convert point => LabelMap.statement convertLabel
      (StoreIso.statement (convertIso C) (Unary.program .halt point))
  | .done => caller

def collectConfiguration (before : L01_3_5_TABLE_NatSerializer019.State (C×Unary.Registers)) : State C :=
  LabelMap.configuration collectLabel before

def convertConfiguration (before : Unary.State (C×RatInput.Store)) : State C :=
  LabelMap.configuration convertLabel (StoreIso.configuration (convertIso C) before)

def support : Finset Label := Finset.univ

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt support body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C:=C) .halt) support :=
  ⟨Finset.mem_univ _,fun point _ => supports_stmt (program .halt point)⟩

theorem finiteStore [Finite C] : Finite (Store C) := inferInstance

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point) ≤ 9 := by
  cases point with
  | collect point =>
    rw [program,LabelMap.statement_actions]
    exact L01_3_5_TABLE_NatSerializer019.collect_program_actions point
  | convert point =>
    rw [program,LabelMap.statement_actions,StoreIso.statement_actions]
    exact (Unary.syntax_actions point).trans (by decide)
  | done => exact Nat.zero_le _

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point) ≤ 7 := by
  cases point with
  | collect point =>
    rw [program,LabelMap.statement_pushes]
    exact L01_3_5_TABLE_NatSerializer019.collect_program_pushes point
  | convert point =>
    rw [program,LabelMap.statement_pushes,StoreIso.statement_pushes]
    exact (Unary.syntax_pushes point).trans (by decide)
  | done => exact Nat.zero_le _

end RootL01.SymbolicSource.PacketUnary
