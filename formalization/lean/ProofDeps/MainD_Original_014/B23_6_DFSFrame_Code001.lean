module
public import RootB234_Cells_Public_003

/-! Fixed fourteen-field physical DFS frame program. Every runtime cell is
Bool. Parent payload and old frame tail reside solely on the physical stacks.
The two scratch flags distinguish an absent pop from a FALSE payload. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace B23_6.DFSFrame
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM

abbrev Stack := RatInput.Stack
abbrev Field := Fin 14
abbrev Bank := Stack → List Bool
abbrev Store (C : Type*) := RootB234.Cells.Store C

inductive Label where
  | pushBoot (kind : Bool) | pushHeader (kind : Bool)
  | saveStart (position : Fin 15) | encode (field : Field) | copySeed (field : Field)
  | pushDone
  | popBoot | clearParent (field : Field) | decode (field : Field) | readKind
  | popDone (kind : Bool)
  | parkClear15 | parkClear12 | park10To12 | park12To15
  deriving DecidableEq, Fintype, Inhabited

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)
variable {C : Type*}

/-- Fourteen literal ROM addresses; 13 is spool and 15 scratch/return. -/
def field (i : Field) : Stack := if h : i.val<13 then ⟨i.val,by omega⟩ else 14
def seed (i : Field) : Bool := decide (field i=0 ∨ field i=1 ∨ field i=2 ∨ field i=4 ∨ field i=11)
def nextSave (i : Field) : Label := .saveStart ⟨i.val+1,by omega⟩
def nextPop (i : Field) : Label :=
  if h : i.val=0 then .readKind else .clearParent ⟨i.val-1,by omega⟩

def clean (memory : Store C) : Store C := (memory.1,false,false)
def state (point : Label) (memory : Store C) (before : Bank) : State C := ⟨some point,memory,before⟩

/-- Literal mature Cells clear body with static stack/label renaming. -/
def clearBody (slot : Stack) (again next : Label) : Statement C :=
  LabelMap.statement (fun point : RootB234.Cells.Label => if point=0 then again else next)
    (StackIso.statement (Equiv.swap 0 slot) (RootB234.Cells.body .clear0))

/-- Literal mature Cells reverse body; the isomorphism is static ROM. -/
def reverseBody (roles : Stack ≃ Stack) (again next : Label) : Statement C :=
  LabelMap.statement (fun point : RootB234.Cells.Label => if point=3 then again else next)
    (StackIso.statement roles (RootB234.Cells.body .reverse13To3))

theorem clearBody_literal (slot : Stack) (again next : Label) :
    clearBody (C:=C) slot again next =
      .pop slot RatDrop.capture (.branch (fun memory => memory.2.1)
        (.goto (fun _ => again)) (.goto (fun _ => next))) := by
  change (TM2.Stmt.pop ((Equiv.swap (0 : Stack) slot) 0) RatDrop.capture
    (.branch (fun memory => memory.2.1) (.goto (fun _ => again)) (.goto (fun _ => next))) : Statement C) = _
  rw [Equiv.swap_apply_left]

theorem reverseBody_literal (roles : Stack ≃ Stack) (again next : Label) :
    reverseBody (C:=C) roles again next =
      .pop (roles 13) RatDrop.capture (.branch (fun memory => memory.2.1)
        (.push (roles 3) RatDrop.bit (.goto (fun _ => again))) (.goto (fun _ => next))) := by
  change LabelMap.statement _ (StackIso.statement roles
    (.pop 13 RatDrop.capture (.branch (fun memory => memory.2.1)
      (.push 3 RatDrop.bit (.goto (fun _ => (3 : RootB234.Cells.Label))))
      (.goto (fun _ => (4 : RootB234.Cells.Label)))))) = _
  rfl

def seedRoles (i : Field) : Stack ≃ Stack := (Equiv.swap 13 15).trans (Equiv.swap 3 (field i))
def park10Roles : Stack ≃ Stack := (Equiv.swap 13 10).trans (Equiv.swap 3 12)
def park12Roles : Stack ≃ Stack := (Equiv.swap 13 12).trans (Equiv.swap 3 15)

def keepSeed (i : Field) (next : Statement C) : Statement C := if seed i then .push 15 RatDrop.bit next else next

def program (pushCaller goodCaller badCaller : Statement C) : Label → Statement C
  | .pushBoot kind => clearBody 15 (.pushBoot kind) (.pushHeader kind)
  | .pushHeader kind => .push 13 (fun _ => kind) (.goto (fun _ => .saveStart 0))
  | .saveStart position =>
      if h : position.val<14 then
        .push 13 (fun _ => false) (.push 13 (fun _ => false) (.goto (fun _ => .encode ⟨position.val,h⟩)))
      else .load clean (.push 13 (fun _ => false) (.goto (fun _ => .pushDone)))
  | .encode i => .pop (field i) RatDrop.capture (.branch (fun memory => memory.2.1)
      (keepSeed i (.push 13 RatDrop.bit (.push 13 (fun _ => true) (.goto (fun _ => .encode i)))))
      (.goto (fun _ => if seed i then .copySeed i else nextSave i)))
  | .copySeed i => reverseBody (seedRoles i) (.copySeed i) (nextSave i)
  | .pushDone => pushCaller
  | .popBoot => .pop 13 RatDrop.capture (.goto (fun _ => .clearParent 13))
  | .clearParent i => clearBody (field i) (.clearParent i) (.decode i)
  | .decode i => .pop 13 RatDrop.capture (.branch RatDrop.bit
      (.pop 13 RatDrop.capture (.push (field i) RatDrop.bit (.goto (fun _ => .decode i))))
      (.pop 13 RatDrop.capture (.goto (fun _ => nextPop i))))
  | .readKind => .pop 13 RatDrop.capture (.branch RatDrop.bit
      (.load clean (.goto (fun _ => .popDone true))) (.load clean (.goto (fun _ => .popDone false))))
  | .popDone true => goodCaller
  | .popDone false => badCaller
  | .parkClear15 => clearBody 15 .parkClear15 .parkClear12
  | .parkClear12 => clearBody 12 .parkClear12 .park10To12
  | .park10To12 => reverseBody park10Roles .park10To12 .park12To15
  | .park12To15 => reverseBody park12Roles .park12To15 .popBoot

def source : Label → Statement C := program .halt .halt .halt
def Interior (point : Label) : Prop := point≠.pushDone ∧ point≠.popDone true ∧ point≠.popDone false
instance (point : Label) : Decidable (Interior point) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem field_ne13 (i : Field) : field i≠13 := by
  unfold field
  split_ifs with h
  · intro equal;have := congrArg Fin.val equal;change i.val=13 at this;omega
  · decide
theorem field_ne15 (i : Field) : field i≠15 := by
  unfold field
  split_ifs with h
  · intro equal;have := congrArg Fin.val equal;change i.val=15 at this;omega
  · decide
theorem field_injective : Function.Injective field := by
  intro i j equal
  unfold field at equal
  split_ifs at equal with hi hj hj
  · exact Fin.ext (congrArg (fun x : Stack => x.val) equal)
  · have := congrArg Fin.val equal;change i.val=14 at this;omega
  · have := congrArg Fin.val equal;change 14=j.val at this;omega
  · apply Fin.ext;omega

theorem seedRoles_source (i : Field) : seedRoles i 13=15 := by
  simp [seedRoles,Equiv.swap_apply_def,Ne.symm (field_ne15 i)]
theorem seedRoles_target (i : Field) : seedRoles i 3=field i := by
  change (Equiv.swap 3 (field i)) ((Equiv.swap (13 : Stack) 15) 3)=field i
  change (Equiv.swap 3 (field i)) 3=field i
  exact Equiv.swap_apply_left 3 (field i)
theorem park10_source : park10Roles 13=10 := rfl
theorem park10_target : park10Roles 3=12 := rfl
theorem park12_source : park12Roles 13=12 := rfl
theorem park12_target : park12Roles 3=15 := rfl

private theorem closed (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro memory;exact Finset.mem_univ _
  | halt => trivial

theorem supports (pushCaller goodCaller badCaller : Statement C) :
    TM2.Supports (program pushCaller goodCaller badCaller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => closed _⟩
theorem finite_store [Finite C] : Finite (Store C) := inferInstance
theorem store_card [Fintype C] : Fintype.card (Store C)=4*Fintype.card C := by
  simp only [Store,RootB234.Cells.Store,RatOutput.Store,Fintype.card_prod,Fintype.card_bool]
  omega

end B23_6.DFSFrame
