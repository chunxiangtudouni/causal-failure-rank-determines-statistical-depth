module

public import RootB234_PrepEntry_StageChannelsPublic_069

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.NatPacket

open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

abbrev Store (C : Type*) := RootB234.RatPacketTransport.Store C

inductive Label where
  | field
  | reverse
  | done
  deriving DecidableEq
instance : Fintype Label where
  elems := {.field,.reverse,.done}
  complete := by intro point; cases point <;> simp
instance : Inhabited Label := ⟨.field⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def fieldLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=1 then .field else .reverse
def reverseLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .done else .reverse

/-- Exactly the frozen single flagged-field parser and frozen whole
temporary reverse. Only the static labels change. NatField's two00
footer cells are genuinely consumed/copied, including canonical zero. -/
def program (copy : Bool) (caller : Statement C) : Label → Statement C
  | .field => LabelMap.statement fieldLabel (RootB234.RatPacketTransport.program copy .halt 1)
  | .reverse => LabelMap.statement reverseLabel (RootB234.RatPacketTransport.program copy .halt 3)
  | .done => caller

def fieldCfg (before : RootB234.RatPacketTransport.State C) : State C := LabelMap.configuration fieldLabel before
def reverseCfg (before : RootB234.RatPacketTransport.State C) : State C := LabelMap.configuration reverseLabel before

def entry (background : RatInput.Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (source target : List Bool) : State C :=
  fieldCfg (RootB234.RatPacketTransport.state background 1 context memory (NatField.packet number source) [] target)

def finalState (copy : Bool) (background : RatInput.Stack → List Bool) (context : C)
    (number : Nat) (source target : List Bool) : State C :=
  reverseCfg (RootB234.RatPacketTransport.state background 4 context (false,false)
    (if copy then NatField.packet number source else source) [] (NatField.packet number target))

def Work (slot : RatInput.Stack) : Prop := slot=2 ∨ slot=4 ∨ slot=15
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work; infer_instance

theorem program_accesses (copy : Bool) (point : Label) : Frame.AccessesOnly Work (program (C := C) copy .halt point) := by
  cases copy <;> cases point <;> exact of_decide_eq_true rfl

theorem program_actions (copy : Bool) (point : Label) : ScannerClock.actions (program (C := C) copy .halt point)≤4 := by
  cases copy <;> cases point <;> exact of_decide_eq_true rfl

theorem program_pushes (copy : Bool) (point : Label) : AuxWorkspace.pushes (program (C := C) copy .halt point)≤2 := by
  cases copy <;> cases point <;> exact of_decide_eq_true rfl

private theorem accesses_writes (body : Statement C) (good : Frame.AccessesOnly Work body) : StackIso.WritesOnly Work body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih => exact ⟨good.1,ih good.2⟩
  | peek _ _ _ ih => exact ih good.2
  | load _ _ ih => exact ih good
  | branch _ _ _ yes no => exact ⟨yes good.1,no good.2⟩
  | goto _ | halt => trivial

theorem program_writes (copy : Bool) (point : Label) : StackIso.WritesOnly Work (program (C := C) copy .halt point) :=
  accesses_writes _ (program_accesses copy point)

theorem program_readonly (copy : Bool) (point : Label) :
    RawGetter.Readonly (fun memory : Store C => memory.1) (program copy .halt point) := by
  cases copy <;> cases point
  all_goals
    dsimp [program,LabelMap.statement,RootB234.RatPacketTransport.program,RootB234.RatPacketTransport.keepSource,
      RootB234.RatPacketTransport.roles,StackIso.statement,RawGetter.Readonly,RatDrop.fieldBody,RatDrop.put,
      RatDrop.capture,RatDrop.bit]
    repeat' constructor
    all_goals (intros; rfl)

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports (copy : Bool) : TM2.Supports (program (C := C) copy .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end RootB234.PrepEntry.NatPacket
