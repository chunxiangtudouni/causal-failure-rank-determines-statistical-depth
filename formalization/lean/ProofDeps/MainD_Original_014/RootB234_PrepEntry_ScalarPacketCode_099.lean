module

public import RootB234_PrepEntry_MainExponentPublic_097

/-! Scalar calls use every live archive bank. Dispose exactly one
canonical packet with the frozen no-copy field loops, without a sink
stack. The sign probe restores the actually popped TRUE header. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.ScalarPacket
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep
variable {C : Type*}

abbrev Store (C : Type*) := C×RatOutput.Store
inductive Label where
  | natural | rational | field (last : Bool) | denominator | sign | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.rational⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

def headerLabel (point : RatDrop.Label) : Label := if point=3 then .rational else .field false
def fieldLabel (last : Bool) (point : RatDrop.Label) : Label :=
  if point=4 then .field last else if last then .done else .denominator
def denominatorLabel (point : RatDrop.Label) : Label := if point=5 then .denominator else .done

def program (caller : Statement C) : Label → Statement C
  | .natural => .goto (fun _ => .field true)
  | .rational => LabelMap.statement headerLabel (RatDrop.headerBody false 4)
  | .field last => LabelMap.statement (fieldLabel last) (RatDrop.fieldBody false 4 5)
  | .denominator => LabelMap.statement denominatorLabel (RatDrop.fieldBody false 5 6)
  | .sign => .pop 15 RatDrop.capture (.peek 15 RatDrop.capture
      (.push 15 (fun _ => true) (.goto (fun _ => .done))))
  | .done => caller

def bank (background : RatInput.Stack→List Bool) (source : List Bool) : RatInput.Stack→List Bool :=
  Function.update background 15 source
def state (point : Label) (context : C) (memory : RatOutput.Store)
    (background : RatInput.Stack→List Bool) (source : List Bool) : State C :=
  ⟨some point,(context,memory),bank background source⟩

def Work (slot : RatInput.Stack) : Prop := slot=15
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work;infer_instance

theorem program_accesses (point : Label) : Frame.AccessesOnly Work (program (C:=C) .halt point) := by
  cases point <;> exact of_decide_eq_true rfl

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point)≤3 := by
  cases point <;> exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point)≤1 := by
  cases point <;> exact of_decide_eq_true rfl

private theorem accesses_writes (body : Statement C) (good : Frame.AccessesOnly Work body) :
    StackIso.WritesOnly Work body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih => exact ⟨good.1,ih good.2⟩
  | peek _ _ _ ih => exact ih good.2
  | load _ _ ih => exact ih good
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) :=
  accesses_writes _ (program_accesses point)

theorem program_readonly (point : Label) :
    RawGetter.Readonly (fun memory : Store C => memory.1) (program .halt point) := by
  cases point
  all_goals dsimp [program,LabelMap.statement,RatDrop.headerBody,RatDrop.fieldBody,RatDrop.put,
    RatDrop.capture,RawGetter.Readonly]
  all_goals repeat' constructor
  all_goals intros;rfl

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _;exact Finset.mem_univ _
  | halt => trivial

theorem supports (caller : Statement C) : TM2.Supports (program caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => supports_stmt (program caller point)⟩

theorem finite_store [Finite C] : Finite (Store C) := inferInstance

end RootB234.PrepEntry.ScalarPacket
