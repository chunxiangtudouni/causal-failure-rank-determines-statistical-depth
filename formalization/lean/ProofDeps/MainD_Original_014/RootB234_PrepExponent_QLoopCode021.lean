module

public import RootB234_PrepExponent_NCountCode015
public import RootB234_PrepExponent_ArithmeticCalls012

/-! One fixed real Q source. First archive budget15 on7 and prepend
literal12. Build actual unary N from8, then decrement11 by a real pop.
Each positive round copies Q, multiplies by literal2, discards only the
old Q packet and parks the real new result. No N selects code or store. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.QLoop
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource

abbrev Stack := RatInput.Stack
abbrev Store (C : Type*) := NCount.Store (Arithmetic.Aux×C)

def arithmeticIso (C : Type*) : Arithmetic.Store (PacketUnary.Store C) ≃ Store C where
  toFun := fun v => ((((v.1,v.2.1.1.1),v.2.1.1.2),v.2.1.2),v.2.2)
  invFun := fun v => (v.1.1.1.1,(((v.1.1.1.2,v.1.1.2),v.1.2),v.2))
  left_inv := by rintro ⟨aux,⟨⟨⟨context,registers⟩,rat⟩,flags⟩⟩;rfl
  right_inv := by rintro ⟨⟨⟨⟨aux,context⟩,registers⟩,rat⟩,flags⟩;rfl

inductive Label where
  | budget : RatPacketTransport.Label → Label
  | literalQ
  | count : NCount.Label → Label
  | take
  | copyQ : RatPacketTransport.Label → Label
  | literalTwo
  | mul : RatBinary.Label → Label
  | discardOld : RatPacketTransport.Label → Label
  | clearOld : Cells.Label → Label
  | parkNew : RatPacketTransport.Label → Label
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.budget 0⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)
variable {C : Type*}

def parkRoles : Stack ≃ Stack := (Equiv.swap 2 7).trans (Equiv.swap 4 3)
def copyRoles : Stack ≃ Stack := ((Equiv.swap 15 7).trans (Equiv.swap 2 15)).trans (Equiv.swap 4 3)
def discardRoles : Stack ≃ Stack := ((Equiv.swap 15 7).trans (Equiv.swap 2 12)).trans (Equiv.swap 4 3)
def clearRoles : Stack ≃ Stack := Equiv.swap 0 12

def budgetLabel (point : RatPacketTransport.Label) : Label := if point=4 then .literalQ else .budget point
def countLabel (point : NCount.Label) : Label := if point=.done then .take else .count point
def copyLabel (point : RatPacketTransport.Label) : Label := if point=4 then .literalTwo else .copyQ point
def mulLabel (point : RatBinary.Label) : Label := if point=.done then .discardOld 0 else .mul point
def discardLabel (point : RatPacketTransport.Label) : Label := if point=4 then .clearOld 0 else .discardOld point
def clearLabel (point : Cells.Label) : Label := if point=6 then .parkNew 0 else .clearOld point
def parkLabel (point : RatPacketTransport.Label) : Label := if point=4 then .take else .parkNew point

def prepend (slot : Stack) : List Bool → Statement C → Statement C
  | [],tail => tail
  | bit::later,tail => prepend slot later (.push slot (fun _ => bit) tail)

def capture (memory : Store C) (cell : Option Bool) : Store C := (memory.1,cell.isSome,cell.getD false)
def present (memory : Store C) : Bool := memory.2.1

def program (caller : Statement C) : Label → Statement C
  | .budget point => LabelMap.statement budgetLabel
      (StackIso.statement parkRoles (RatPacketTransport.program false .halt point))
  | .literalQ => prepend 7 (RatInput.Encoder.packet (12 : Rat) []) (.goto (fun _ => .count default))
  | .count point => LabelMap.statement countLabel (NCount.program .halt point)
  | .take => .pop 11 capture (.branch present (.goto (fun _ => .copyQ 0)) (.goto (fun _ => .done)))
  | .copyQ point => LabelMap.statement copyLabel
      (StackIso.statement copyRoles (RatPacketTransport.program true .halt point))
  | .literalTwo => prepend 15 (RatInput.Encoder.packet (2 : Rat) []) (.goto (fun _ => .mul default))
  | .mul point => LabelMap.statement mulLabel
      (StoreIso.statement (arithmeticIso C) (Arithmetic.mulProgram point))
  | .discardOld point => LabelMap.statement discardLabel
      (StackIso.statement discardRoles (RatPacketTransport.program false .halt point))
  | .clearOld point => LabelMap.statement clearLabel
      (StackIso.statement clearRoles (Cells.Public.clear0 point))
  | .parkNew point => LabelMap.statement parkLabel
      (StackIso.statement parkRoles (RatPacketTransport.program false .halt point))
  | .done => caller

theorem prepend_step (slot : Stack) (cells : List Bool) (next : Statement C)
    (memory : Store C) (before : Stack → List Bool) :
    TM2.stepAux (prepend slot cells next) memory before=
      TM2.stepAux next memory (Function.update before slot (cells++before slot)) := by
  induction cells generalizing next with
  | nil => simp only [prepend,List.nil_append,Function.update_eq_self]
  | cons bit later ih =>
    rw [prepend,ih]
    simp only [TM2.stepAux,Function.update_self,Function.update_idem,List.cons_append]

theorem take_positive (caller : Statement C) (memory : Store C) (before : Stack → List Bool)
    (tail : List Bool) (source : before 11=true::tail) :
    TM2.step (program caller) (⟨some .take,memory,before⟩ : State C)=
      some ⟨some (.copyQ 0),(memory.1,true,true),Function.update before 11 tail⟩ := by
  simp only [TM2.step,program,TM2.stepAux,source,capture,present,List.head?_cons,List.tail_cons]
  rfl

theorem take_zero (caller : Statement C) (memory : Store C) (before : Stack → List Bool)
    (source : before 11=[]) :
    TM2.step (program caller) (⟨some .take,memory,before⟩ : State C)=
      some ⟨some .done,(memory.1,false,false),before⟩ := by
  simp only [TM2.step,program,TM2.stepAux,source,capture,present,List.head?_nil,List.tail_nil]
  change some (⟨some .done,(memory.1,false,false),Function.update before 11 []⟩ : State C)=_
  rw [←source,Function.update_eq_self]

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

end RootB234.PrepExponent.QLoop
