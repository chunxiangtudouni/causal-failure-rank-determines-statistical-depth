module

public import RootB234_PrepEntry_BudgetPublic_029

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.NatPrefix

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

abbrev Store (C : Type*) := Alpha.Store C

inductive Label where
  | check
  | parse : Fin 2 → Label
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.check⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def capture (memory : Store C) (value : Option Bool) : Store C :=
  (memory.1,(0,value.getD false))

def parseLabel (point : Fin 2) : Label := if point=1 then .check else .parse point

/-- The original Datum tag selects the frozen natural parser. Each restart
of its finite control is an actual peek/load operation; the rational tag
is left unread. No numeric count, width or stopping fuel is in this code. -/
def program (caller : Statement C) : Label → Statement C
  | .check => .peek 0 capture (.branch (fun memory => memory.2.2)
      (.goto (fun _ => .done)) (.goto (fun _ => .parse 0)))
  | .parse point => LabelMap.statement parseLabel (Alpha.program .halt point)
  | .done => caller

def parseCfg (before : Alpha.State C) : State C := LabelMap.configuration parseLabel before

def tape (bank : RatInput.Stack → List Bool) : Tape Bool :=
  Tape.mk' (ListBlank.mk (bank 1)) (ListBlank.mk (bank 0))

def naturals (numbers : List Nat) : List Bool :=
  numbers.flatMap (fun number => encodeDatum (.natural number))

def archived (left : List Bool) (numbers : List Nat) : List Bool :=
  numbers.foldl Alpha.nextLeft left

def payloadMass (numbers : List Nat) : Nat :=
  (numbers.map (fun number => (PSTRTMNatValue017.rawPayload number).length)).sum

def workTime (numbers : List Nat) : Nat :=
  (numbers.map (fun number =>
    (PSTRTMNatValue017.rawPayload number).length^2+
      9*(PSTRTMNatValue017.rawPayload number).length+7)).sum+2

theorem parse_path (caller : Statement C) (trace : List (Alpha.State C))
    (before final : Alpha.State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (Alpha.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some 1) :
    (trace.map parseCfg).head?=some (parseCfg before) ∧
    (trace.map parseCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map parseCfg).getLast?=some (parseCfg final) := by
  have proper:=NativeMulLink.no_early_halt_port (Alpha.program .halt) 1 rfl trace final chain last active
  have mapped:=LabelMap.actual_path_on parseLabel (Alpha.program .halt) (program caller)
    trace before final first chain last (by
      intro current member point selected
      have notDone : point≠1 := by intro same; subst point; exact proper current member selected
      simp only [parseLabel,notDone,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem natural_head (bank : RatInput.Stack → List Bool) (left : List Bool)
    (number : Nat) (suffix : List Bool)
    (physical : tape bank=Tape.mk₂ left (encodeDatum (.natural number)++suffix)) :
    (bank 0).head?.getD false=false := by
  have head:=congrArg Tape.head physical
  have same : (bank 0).head?.getD false=(bank 0).headI := by cases bank 0 <;> rfl
  rw [same]
  simpa only [tape,Tape.mk'_head,ListBlank.head_mk,Tape.mk₂,encodeDatum,
    List.cons_append,List.headI_cons] using head

theorem rational_head (bank : RatInput.Stack → List Bool) (left : List Bool)
    (x : Rat) (suffix : List Bool)
    (physical : tape bank=Tape.mk₂ left (encodeDatum (.rational x)++suffix)) :
    (bank 0).head?.getD false=true := by
  have head:=congrArg Tape.head physical
  have same : (bank 0).head?.getD false=(bank 0).headI := by cases bank 0 <;> rfl
  rw [same]
  simpa only [tape,Tape.mk'_head,ListBlank.head_mk,Tape.mk₂,encodeDatum,
    List.cons_append,List.headI_cons] using head

theorem natural_step (caller : Statement C) (context : C) (memory : Alpha.NativeMemory)
    (bank : RatInput.Stack → List Bool) (left : List Bool) (number : Nat) (suffix : List Bool)
    (physical : tape bank=Tape.mk₂ left (encodeDatum (.natural number)++suffix)) :
    TM2.step (program caller) (⟨some .check,(context,memory),bank⟩ : State C)=
      some (parseCfg (⟨some 0,(context,(0,false)),bank⟩ : Alpha.State C)) := by
  have head:=natural_head bank left number suffix physical
  simp only [TM2.step,program,TM2.stepAux,capture,head,parseCfg,LabelMap.configuration]
  rfl

theorem rational_step (caller : Statement C) (context : C) (memory : Alpha.NativeMemory)
    (bank : RatInput.Stack → List Bool) (left : List Bool) (x : Rat) (suffix : List Bool)
    (physical : tape bank=Tape.mk₂ left (encodeDatum (.rational x)++suffix)) :
    TM2.step (program caller) (⟨some .check,(context,memory),bank⟩ : State C)=
      some (⟨some .done,(context,(0,true)),bank⟩ : State C) := by
  have head:=rational_head bank left x suffix physical
  simp only [TM2.step,program,TM2.stepAux,capture,head]
  rfl

def Work (slot : RatInput.Stack) : Prop := slot=0 ∨ slot=1
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work; infer_instance

theorem program_accesses (point : Label) : Frame.AccessesOnly Work (program (C := C) .halt point) := by
  cases point with
  | check | done => exact of_decide_eq_true rfl
  | parse point => fin_cases point <;> exact of_decide_eq_true rfl

theorem program_actions (point : Label) : ScannerClock.actions (program (C := C) .halt point)≤8 := by
  cases point with
  | check | done => exact of_decide_eq_true rfl
  | parse point => fin_cases point <;> exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := C) .halt point)≤8 := by
  cases point with
  | check | done => exact of_decide_eq_true rfl
  | parse point => fin_cases point <;> exact of_decide_eq_true rfl

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end RootB234.PrepEntry.NatPrefix
