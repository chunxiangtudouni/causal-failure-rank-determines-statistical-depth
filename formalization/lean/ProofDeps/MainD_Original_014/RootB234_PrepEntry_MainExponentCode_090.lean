module

public import RootB234_PrepEntry_WholeChannelsPublic_075
public import RootB234_PrepEntry_NatPacketPublic_081
public import RootB234_PrepExponent_GlobalRun040

/-! One original-input control graph. Produce E immediately after the
actual metadata/restoration producer, where all local work banks really
are empty. Move the actual E11 packet to5 and really clear the Q/budget
scratch7 before the existing original-input dual-channel front. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.MainExponent
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep RootB234.PrepExponent
open RootL01.SymbolicSource
variable {C D : Type*}

abbrev Store (C : Type*) := Budget.Store (Global.Store (StageChannels.Store C))
abbrev Outer := Budget.Store Unit×Global.Store Unit
abbrev ExponentContext (C : Type*) := Budget.Store Unit×StageChannels.Store C
abbrev ExponentCore (C : Type*) := PacketUnary.Store (Arithmetic.Aux×ExponentContext C)

def mapGlobalContext (change : C → D) (memory : Global.Store C) : Global.Store D :=
  ((((memory.1.1.1.1,change memory.1.1.1.2),memory.1.1.2),memory.1.2),memory.2)

def globalFlat (C : Type*) : Global.Store C ≃ Global.Store Unit×C where
  toFun := fun memory => (mapGlobalContext (fun _ => ()) memory,QLoop.rootContext memory)
  invFun := fun memory => mapGlobalContext (fun _ => memory.2) memory.1
  left_inv := by intro memory;rfl
  right_inv := by
    rintro ⟨⟨⟨⟨⟨aux,trivial⟩,registers⟩,rat⟩,flags⟩,context⟩
    cases trivial;rfl

def budgetFlat (C : Type*) : Budget.Store C ≃ Budget.Store Unit×C where
  toFun := fun memory => (WholeChannels.mapBudgetContext (fun _ => ()) memory,Budget.callerContext memory)
  invFun := fun memory => WholeChannels.mapBudgetContext (fun _ => memory.2) memory.1
  left_inv := by intro memory;rfl
  right_inv := by
    rintro ⟨⟨⟨⟨⟨⟨trivial,raw⟩,copy⟩,alpha⟩,natural⟩,header⟩,context⟩
    cases trivial;rfl

def stageIso (C : Type*) : (Outer×StageChannels.Store C) ≃ Store C :=
  (((budgetFlat (Global.Store (StageChannels.Store C))).trans
    (Equiv.prodCongr (Equiv.refl (Budget.Store Unit)) (globalFlat (StageChannels.Store C)))).trans
      (Equiv.prodAssoc (Budget.Store Unit) (Global.Store Unit) (StageChannels.Store C)).symm).symm

def exponentIso (C : Type*) : Global.Store (ExponentContext C) ≃ Store C :=
  (((globalFlat (ExponentContext C)).trans
    (Equiv.prodAssoc (Global.Store Unit) (Budget.Store Unit) (StageChannels.Store C)).symm).trans
      (Equiv.prodCongr (Equiv.prodComm (Global.Store Unit) (Budget.Store Unit)) (Equiv.refl (StageChannels.Store C)))).trans
        (stageIso C)

inductive Label where
  | budget : Budget.Label → Label
  | exponent : Global.Label → Label
  | natural : NatPacket.Label → Label
  | clear : Cells.Label → Label
  | channels : StageChannels.Label → Label
  | done
  deriving DecidableEq,Fintype
instance : Inhabited Label := ⟨.budget default⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

def naturalRoles : RatInput.Stack ≃ RatInput.Stack := (Equiv.swap 15 11).trans (Equiv.swap 2 5)
def clearRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 0 7
def budgetLabel (point : Budget.Label) : Label := if point=.done then .exponent default else .budget point
def exponentLabel (point : Global.Label) : Label := if point=.done then .natural default else .exponent point
def naturalLabel (point : NatPacket.Label) : Label := if point=.done then .clear 0 else .natural point
def clearLabel (point : Cells.Label) : Label := if point=6 then .channels default else .clear point
def channelsLabel (point : StageChannels.Label) : Label := if point=.done then .done else .channels point

noncomputable def program (caller : Statement C) : Label → Statement C
  | .budget point => LabelMap.statement budgetLabel (Budget.program .halt point)
  | .exponent point => LabelMap.statement exponentLabel (StoreIso.statement (exponentIso C) (Global.program .halt point))
  | .natural point => LabelMap.statement naturalLabel (StoreIso.statement (exponentIso C)
      (StackIso.statement naturalRoles (NatPacket.program false .halt point)))
  | .clear point => LabelMap.statement clearLabel (StoreIso.statement (exponentIso C)
      (StackIso.statement clearRoles (Cells.Public.clear0 point)))
  | .channels point => LabelMap.statement channelsLabel (StoreIso.statement (stageIso C)
      (ContextLift.statement (StageChannels.program .halt point)))
  | .done => caller

def globalMemory (context : C) : Global.Store (StageChannels.Store C) :=
  mapGlobalContext (fun _ => WholeChannels.stageMemory context) (default : Global.Store Unit)

def entry (context : C) (bits : List Bool) : State C :=
  LabelMap.configuration budgetLabel (Budget.entry (globalMemory context) bits)

def callerContext (memory : Store C) : C :=
  StageChannels.callerContext (QLoop.rootContext (Budget.callerContext memory))

instance [Inhabited C] : Inhabited (Store C) := ⟨(Budget.entry (globalMemory (default : C)) []).var⟩

theorem initial_default [Inhabited C] (bits : List Bool) :
    entry (default : C) bits=TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Store C) 0 bits := by
  change (⟨some (default : Label),(default : Store C),_⟩ : State C)=⟨some default,default,_⟩
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem exponent_context (memory : Global.Store (ExponentContext C)) :
    callerContext (exponentIso C memory)=StageChannels.callerContext (QLoop.rootContext memory).2 := rfl

theorem stage_context (memory : Outer) (stage : StageChannels.Store C) :
    callerContext (stageIso C (memory,stage))=StageChannels.callerContext stage := rfl

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _;exact Finset.mem_univ _
  | halt => trivial

theorem supports (caller : Statement C) : TM2.Supports (program caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => supports_stmt (program caller point)⟩

theorem finite_store [Fintype C] : Finite (Store C) := by
  let : Fintype (StageChannels.Store C) := inferInstance
  let : Finite (Global.Store (StageChannels.Store C)) := Global.finite_store
  let : Fintype (Global.Store (StageChannels.Store C)) := Fintype.ofFinite _
  infer_instance

end RootB234.PrepEntry.MainExponent
