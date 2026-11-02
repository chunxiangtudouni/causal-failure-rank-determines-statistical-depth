module

public import B23_4_RatWordPrep_SeqCmp_OddsInitCode_111
public import B23_4_RatWordPrep_SeqCmp_LookupChannel_101

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

abbrev Store (C : Type*) := FullStore.Store C
abbrev PacketContext (C : Type*) := OddsInit.PacketContext C

inductive Label where
  | init : OddsInit.Label → Label
  | check
  | falseLookup : Lookup.Label → Label
  | trueLookup : Lookup.Label → Label
  | ratio : RatBinary.Label → Label
  | multiply : RatBinary.Label → Label
  | dropQuery : RootB234.RatPacketTransport.Label → Label
  | clearQuery : RootB234.Cells.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.init default⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def queryRoles : RatInput.Stack ≃ RatInput.Stack := (Equiv.swap 15 0).trans (Equiv.swap 2 3)
def clearRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 0 3
def capture (memory : Store C) (cell : Option Bool) : Store C := (memory.1,WordFields.capture memory.2 cell)
def present (memory : Store C) : Bool := WordFields.present memory.2

def initLabel (point : OddsInit.Label) : Label := if point=.done then .check else .init point
def falseLabel (point : Lookup.Label) : Label := if point=.done then .trueLookup .boot else .falseLookup point
def trueLabel (point : Lookup.Label) : Label := if point=.done then .ratio default else .trueLookup point
def ratioLabel (point : RatBinary.Label) : Label := if point=.done then .multiply default else .ratio point
def multiplyLabel (point : RatBinary.Label) : Label := if point=.done then .dropQuery 2 else .multiply point
def queryLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .clearQuery 0 else .dropQuery point
def clearLabel (point : RootB234.Cells.Label) : Label := if point=6 then .check else .clearQuery point

/-- One actual symbol loop: two physical channel lookups, normalized
ratio/division, normalized odds/multiplication, actual natural query
disposal, then a real finite EOF test on the remaining symbol queue. -/
noncomputable def program (caller : Statement C) : Label → Statement C
  | .init point => LabelMap.statement initLabel (OddsInit.program .halt point)
  | .check => .peek 0 capture (.branch present (.goto (fun _ => .falseLookup .boot)) (.goto (fun _ => .done)))
  | .falseLookup point => LabelMap.statement falseLabel (ContextLift.statement (Lookup.program false .halt point))
  | .trueLookup point => LabelMap.statement trueLabel (ContextLift.statement (Lookup.program true .halt point))
  | .ratio point => LabelMap.statement ratioLabel (StoreIso.statement (FullStore.divIso C)
      (RatBinary.program RatMulDiv.divSource .halt point))
  | .multiply point => LabelMap.statement multiplyLabel (StoreIso.statement (FullStore.mulIso C)
      (RatBinary.program RatMulDiv.mulSource .halt point))
  | .dropQuery point => LabelMap.statement queryLabel (StoreIso.statement (OddsInit.packetIso C)
      (RootB234.RatPacketTransport.atProgram queryRoles false point))
  | .clearQuery point => LabelMap.statement clearLabel (StoreIso.statement (OddsInit.packetIso C)
      (StackIso.statement clearRoles (RootB234.Cells.Public.clear0 point)))
  | .done => caller

def initCfg (before : OddsInit.State C) : State C := LabelMap.configuration initLabel before
def lookupCfg (truth : Bool) (registers : FullStore.Aux) (before : Lookup.State C) : State C :=
  LabelMap.configuration (if truth then trueLabel else falseLabel) (ContextLift.configuration registers before)
def ratioCfg (before : RatBinary.State (FullStore.DivContext C) RatMulDiv.divStates) : State C :=
  LabelMap.configuration ratioLabel (StoreIso.configuration (FullStore.divIso C) before)
def multiplyCfg (before : RatBinary.State (FullStore.MulContext C) RatMulDiv.mulStates) : State C :=
  LabelMap.configuration multiplyLabel (StoreIso.configuration (FullStore.mulIso C) before)
def packetCfg (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration queryLabel (StoreIso.configuration (OddsInit.packetIso C) before)
def clearCfg (before : RootB234.Cells.State (PacketContext C)) : State C :=
  LabelMap.configuration clearLabel (StoreIso.configuration (OddsInit.packetIso C) before)

def entry (context : C) (bits : List Bool) : State C := initCfg (OddsInit.entry context bits)

theorem initial_default [Inhabited C] (bits : List Bool) :
    entry (default : C) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  rw [entry,OddsInit.initial_default]
  rfl

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end B23_4_RatWordPrep.WordFold
