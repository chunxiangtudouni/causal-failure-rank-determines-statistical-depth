module

public import RootB234_PrepExponent_NatToRatRun006
public import RootL01_SymbolicSource_PacketUnary_Public_031

/-! A real bounded-value N counter: actual copy8, actual reverse6->15,
frozen packet->unary, actual move5->11 and actual clear15. The source is
fixed before N. Local empty banks are caller-owned entry data. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NCount
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource

abbrev Stack := RatInput.Stack
abbrev Store (C : Type*) := PacketUnary.Store C×RatOutput.Store

inductive Label where
  | copy : B23_4_RatWordPrep.WholeCopy.Label → Label
  | reverse : Cells.Label → Label
  | unary : PacketUnary.Label → Label
  | move : Cells.Label → Label
  | clear : Cells.Label → Label
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.copy .boot⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)
variable {C : Type*}

def unaryIso (C : Type*) : PacketUnary.Store (C×RatOutput.Store) ≃ Store C where
  toFun := fun v => (((v.1.1.1,v.1.2),v.2),v.1.1.2)
  invFun := fun v => (((v.1.1.1,v.2),v.1.1.2),v.1.2)
  left_inv := by rintro ⟨⟨⟨context,flags⟩,registers⟩,rat⟩;rfl
  right_inv := by rintro ⟨⟨⟨context,registers⟩,rat⟩,flags⟩;rfl

def copyRoles : Stack ≃ Stack :=
  ((Equiv.swap 0 8).trans (Equiv.swap 2 6)).trans (Equiv.swap 3 4)
def reverseRoles : Stack ≃ Stack := (Equiv.swap 3 6).trans (Equiv.swap 2 15)
def moveRoles : Stack ≃ Stack := (Equiv.swap 3 5).trans (Equiv.swap 2 11)
def clearRoles : Stack ≃ Stack := Equiv.swap 0 15

def copyLabel (point : B23_4_RatWordPrep.WholeCopy.Label) : Label :=
  if point=.done then .reverse 3 else .copy point
def reverseLabel (point : Cells.Label) : Label := if point=4 then .unary (.collect 0) else .reverse point
def unaryLabel (point : PacketUnary.Label) : Label := if point=.done then .move 3 else .unary point
def moveLabel (point : Cells.Label) : Label := if point=4 then .clear 0 else .move point
def clearLabel (point : Cells.Label) : Label := if point=6 then .done else .clear point

def program (caller : Statement C) : Label → Statement C
  | .copy point => LabelMap.statement copyLabel
      (StackIso.statement copyRoles (B23_4_RatWordPrep.WholeCopy.program .halt point))
  | .reverse point => LabelMap.statement reverseLabel
      (StackIso.statement reverseRoles (Cells.Public.reverse3To2 point))
  | .unary point => LabelMap.statement unaryLabel
      (StoreIso.statement (unaryIso C) (PacketUnary.program .halt point))
  | .move point => LabelMap.statement moveLabel
      (StackIso.statement moveRoles (Cells.Public.reverse3To2 point))
  | .clear point => LabelMap.statement clearLabel
      (StackIso.statement clearRoles (Cells.Public.clear0 point))
  | .done => caller

def bank (background : Stack → List Bool) (input backup output counter target : List Bool) : Stack → List Bool :=
  fun slot => if slot=3 then [] else if slot=8 then input else if slot=6 then backup
    else if slot=5 then output else if slot=11 then counter else if slot=15 then target else background slot

def state (background : Stack → List Bool) (point : Label) (memory : Store C)
    (input backup output counter target : List Bool) : State C :=
  ⟨some point,memory,bank background input backup output counter target⟩

def copyCfg (before : B23_4_RatWordPrep.WholeCopy.State (PacketUnary.Store C)) : State C :=
  LabelMap.configuration copyLabel (StackIso.configuration copyRoles before)
def reverseCfg (before : Cells.State (PacketUnary.Store C)) : State C :=
  LabelMap.configuration reverseLabel (StackIso.configuration reverseRoles before)
def unaryCfg (before : PacketUnary.State (C×RatOutput.Store)) : State C :=
  LabelMap.configuration unaryLabel (StoreIso.configuration (unaryIso C) before)
def moveCfg (before : Cells.State (PacketUnary.Store C)) : State C :=
  LabelMap.configuration moveLabel (StackIso.configuration moveRoles before)
def clearCfg (before : Cells.State (PacketUnary.Store C)) : State C :=
  LabelMap.configuration clearLabel (StackIso.configuration clearRoles before)

theorem packet_equal (number : Nat) :
    B23_4_RatWordPrep.NatField.packet number []=L01_3_5_TABLE_FourRecord011.packet number := rfl

theorem copy_state (background : Stack → List Bool) (point : B23_4_RatWordPrep.WholeCopy.Label)
    (memory : Store C) (input backup output counter target : List Bool) :
    copyCfg (B23_4_RatWordPrep.WholeCopy.state
      (StackIso.slots copyRoles.symm (bank background [] [] output counter target))
      point memory input backup (background 4))=
      state background (copyLabel point) memory input backup output counter target := by
  unfold copyCfg B23_4_RatWordPrep.WholeCopy.state LabelMap.configuration StackIso.configuration
  congr 1
  funext slot
  fin_cases slot <;> rfl

private theorem supports_stmt (body : Statement C) :
    TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _;exact Finset.mem_univ _
  | halt => trivial

theorem supports (caller : Statement C) : TM2.Supports (program caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => supports_stmt (program caller point)⟩

theorem finite_store [Finite C] : Finite (Store C) := inferInstance

end RootB234.PrepExponent.NCount
