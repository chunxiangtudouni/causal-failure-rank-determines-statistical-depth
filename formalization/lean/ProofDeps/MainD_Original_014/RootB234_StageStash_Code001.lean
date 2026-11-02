module
public import B23_6_DFSFrame_Public013

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB234.StageStash
open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
abbrev Stack := Fin 16
abbrev Alphabet (_ : Stack) := Bool
abbrev Field := Fin 8
abbrev Bank := Stack → List Bool
abbrev Store (C : Type*) := C×Bool×Bool
inductive Label where
  | start (position : Fin 9) | encode (field : Field) | clear (field : Field) | decode (field : Field)
  | saved | restored
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.start 0⟩
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)
variable {C : Type*}

def field (i : Field) : Stack :=
  if i=0 then 2 else if i=1 then 3 else if i=2 then 5 else if i=3 then 6 else
    if i=4 then 10 else if i=5 then 12 else if i=6 then 13 else 14

def index (slot : Stack) : Nat :=
  if slot=2 then 0 else if slot=3 then 1 else if slot=5 then 2 else if slot=6 then 3 else
    if slot=10 then 4 else if slot=12 then 5 else if slot=13 then 6 else if slot=14 then 7 else 8

def Work (slot : Stack) : Prop := slot=0 ∨ index slot<8
instance (slot : Stack) : Decidable (Work slot) := by unfold Work;infer_instance

def clean (memory : Store C) : Store C := (memory.1,false,false)
def capture (memory : Store C) (value : Option Bool) : Store C := (memory.1,value.isSome,value.getD false)
def state (point : Label) (memory : Store C) (before : Bank) : State C := ⟨some point,memory,before⟩
def nextSave (i : Field) : Label := .start ⟨i.val+1,by omega⟩
def nextRestore (i : Field) : Label := if h : i.val=0 then .restored else .clear ⟨i.val-1,by omega⟩
def program (stashCaller restoreCaller : Statement C) : Label → Statement C
  | .start position =>
    if h : position.val<8 then .push 0 (fun _ => false) (.push 0 (fun _ => false) (.goto (fun _ => .encode ⟨position.val,h⟩)))
    else .load clean (.goto (fun _ => .saved))
  | .encode i => .pop (field i) capture (.branch (fun memory => memory.2.1)
      (.push 0 (fun memory => memory.2.2) (.push 0 (fun _ => true) (.goto (fun _ => .encode i))))
      (.goto (fun _ => nextSave i)))
  | .clear i => .pop (field i) capture (.branch (fun memory => memory.2.1)
      (.goto (fun _ => .clear i)) (.goto (fun _ => .decode i)))
  | .decode i => .pop 0 capture (.branch (fun memory => memory.2.2)
      (.pop 0 capture (.push (field i) (fun memory => memory.2.2) (.goto (fun _ => .decode i))))
      (.pop 0 capture (.load clean (.goto (fun _ => nextRestore i)))))
  | .saved => stashCaller
  | .restored => restoreCaller

def source : Label → Statement C := program .halt .halt
def Interior (point : Label) : Prop := point≠.saved ∧ point≠.restored
instance (point : Label) : Decidable (Interior point) := by unfold Interior;infer_instance

theorem field_ne0 (i : Field) : field i≠0 := by fin_cases i <;> decide
theorem field_index (i : Field) : index (field i)=i.val := by fin_cases i <;> rfl
theorem field_injective : Function.Injective field := by
  intro i j equal
  apply Fin.ext
  simpa only [field_index] using congrArg index equal

theorem protected15 : ¬Work 15 := by decide
theorem protected4 : ¬Work 4 := by decide
theorem label_count : Fintype.card Label=35 := by decide

theorem supports (save restore : Statement C) : TM2.Supports (program save restore) (Finset.univ : Finset Label) := by
  refine ⟨Finset.mem_univ _,?_⟩
  intro point _
  generalize program save restore point=body
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro memory;exact Finset.mem_univ (target memory)
  | halt => trivial

theorem finite_store [Finite C] : Finite (Store C) := inferInstance
end RootB234.StageStash
