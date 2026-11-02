module

public import RootB234_PrepExponent_NatIncrementPublic003
public import B23_4_RatWordPrep_SeqCmp_WholeCopyPublic_045

/-! A static natural-to-rational packet route. WholeCopy produces a
reverse backup on4; the frozen Cells body then really reverses4 into15.
Neither the number nor its digit list is a source-code parameter. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NatToRat
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM PA17TMRatArithmeticParse002

abbrev Stack := RatInput.Stack
abbrev Store (C : Type*) := C × RatOutput.Store

inductive Label where
  | prepare
  | copy : B23_4_RatWordPrep.WholeCopy.Label → Label
  | reverse : Cells.Label → Label
  | header | done
  deriving DecidableEq,Fintype

instance : Inhabited Label := ⟨.prepare⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)
variable {C : Type*}

def copyRoles : Stack ≃ Stack := (Equiv.swap 0 8).trans (Equiv.swap 2 4)
def reverseRoles : Stack ≃ Stack := (Equiv.swap 3 4).trans (Equiv.swap 2 15)

def copyLabel (point : B23_4_RatWordPrep.WholeCopy.Label) : Label :=
  if point=.done then .reverse 3 else .copy point

def reverseLabel (point : Cells.Label) : Label :=
  if point=4 then .header else .reverse point

def program (caller : Statement C) : Label → Statement C
  | .prepare => .push 15 (fun _ => false) (.push 15 (fun _ => false)
      (.push 15 (fun _ => true) (.push 15 (fun _ => true) (.goto (fun _ => .copy .boot)))))
  | .copy point => LabelMap.statement copyLabel
      (StackIso.statement copyRoles (B23_4_RatWordPrep.WholeCopy.program .halt point))
  | .reverse point => LabelMap.statement reverseLabel
      (StackIso.statement reverseRoles (Cells.Public.reverse3To2 point))
  | .header => .push 15 (fun _ => false) (.push 15 (fun _ => true) (.goto (fun _ => .done)))
  | .done => caller

def bank (background : Stack → List Bool) (input scratch backup target : List Bool) : Stack → List Bool :=
  fun point => if point=8 then input else if point=3 then scratch else if point=4 then backup
    else if point=15 then target else background point

def state (background : Stack → List Bool) (point : Label) (memory : Store C)
    (input scratch backup target : List Bool) : State C :=
  ⟨some point,memory,bank background input scratch backup target⟩

theorem step_prepare (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (input scratch backup target : List Bool) :
    TM2.step (program caller) (state background .prepare memory input scratch backup target)=
      some (state background (.copy .boot) memory input scratch backup (true::true::false::false::target)) := by
  change some (⟨some (.copy .boot),memory,_⟩ : State C)=_
  congr 1; congr 1
  funext point;fin_cases point <;> rfl

theorem step_header (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (input scratch backup target : List Bool) :
    TM2.step (program caller) (state background .header memory input scratch backup target)=
      some (state background .done memory input scratch backup (true::false::target)) := by
  change some (⟨some .done,memory,_⟩ : State C)=_
  congr 1; congr 1
  funext point;fin_cases point <;> rfl

def copyCfg (current : B23_4_RatWordPrep.WholeCopy.State C) : State C :=
  LabelMap.configuration copyLabel (StackIso.configuration copyRoles current)

def reverseCfg (current : Cells.State C) : State C :=
  LabelMap.configuration reverseLabel (StackIso.configuration reverseRoles current)

theorem copy_state (background : Stack → List Bool) (point : B23_4_RatWordPrep.WholeCopy.Label)
    (memory : Store C) (input backup scratch target : List Bool) :
    copyCfg (B23_4_RatWordPrep.WholeCopy.state
      (StackIso.slots copyRoles.symm (Function.update background 15 target)) point memory input backup scratch)=
      state background (copyLabel point) memory input scratch backup target := by
  unfold copyCfg LabelMap.configuration StackIso.configuration B23_4_RatWordPrep.WholeCopy.state
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem one_payload : PSTRTMNatValue017.rawPayload 1=[true] := rfl

theorem integer_packet (number : Nat) (tail : List Bool) :
    true::false::(B23_4_RatWordPrep.NatField.packet number [] ++ true::true::false::false::tail)=
      RatInput.Encoder.packet (number : Rat) tail := by
  simp [RatInput.Encoder.packet,PSTRSymbolicRatExport.packet,sign,numeratorDigits,denominatorDigits,
    B23_4_RatWordPrep.NatField.packet,one_payload,PSTRTMRawNat010.leftBlocks,List.append_assoc]

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

end RootB234.PrepExponent.NatToRat
