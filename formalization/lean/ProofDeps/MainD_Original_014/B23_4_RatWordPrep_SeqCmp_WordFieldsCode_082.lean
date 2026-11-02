module

public import B23_4_RatWordPrep_SeqCmp_ChannelsOriginal_081
public import B23_4_RatWordPrep_SeqCmp_NatPacketMove_068

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFields

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

abbrev NatAux := RawNat.ParserMemory × PSTRSymbolicNaturalExport.Store
abbrev Store (C : Type*) := NatAux × Channels.Store C
abbrev RawContext (C : Type*) := NatAux × Channels.RawContext C
abbrev PacketContext (C : Type*) := NatAux × Channels.PacketContext C
abbrev RoundContext (C : Type*) := NatAux × Channels.RoundContext C

inductive Label where
  | channels : Channels.Label → Label
  | target : RawGetter.Label → Label
  | targetMove : RootB234.RatPacketTransport.Label → Label
  | count : RawNat.Label → Label
  | countMove : RootB234.RatPacketTransport.Label → Label
  | build : RootB234.RuntimeCounter.Builder.Label → Label
  | clearCount
  | round : RootB234.RuntimeCounter.Round.Label → Label
  | symbol : RawNat.Label → Label
  | symbolMove : RootB234.RatPacketTransport.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.channels default⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def rawIso (C : Type*) : RawGetter.Store (RawContext C) ≃ Store C where
  toFun := fun v => (v.1.1.1,Channels.rawIso C ((v.1.1.2,v.1.2),v.2))
  invFun := fun v => let old := (Channels.rawIso C).symm v.2
    (((v.1,old.1.1),old.1.2),old.2)
  left_inv := by rintro ⟨⟨⟨natural,rest⟩,parser⟩,exporter⟩; rfl
  right_inv := by rintro ⟨natural,rest⟩; rfl

def packetIso (C : Type*) : RootB234.RatPacketTransport.Store (PacketContext C) ≃ Store C where
  toFun := fun v => (v.1.1,Channels.packetIso C (v.1.2,v.2))
  invFun := fun v => let old := (Channels.packetIso C).symm v.2
    ((v.1,old.1),old.2)
  left_inv := by rintro ⟨⟨natural,rest⟩,flags⟩; rfl
  right_inv := by rintro ⟨natural,rest⟩; rfl

def roundIso (C : Type*) : RootB234.RuntimeCounter.Round.Store (RoundContext C) ≃ Store C where
  toFun := fun v => (v.1.1,Channels.roundIso C (v.1.2,v.2))
  invFun := fun v => let old := (Channels.roundIso C).symm v.2
    ((v.1,old.1),old.2)
  left_inv := by rintro ⟨⟨natural,rest⟩,flags⟩; rfl
  right_inv := by rintro ⟨natural,rest⟩; rfl

def naturalIso (C : Type*) : RawNat.Store (Channels.Store C) ≃ Store C where
  toFun := fun v => ((v.1.2,v.2),v.1.1)
  invFun := fun v => ((v.2,v.1.1),v.1.2)
  left_inv := by rintro ⟨⟨rest,parser⟩,exporter⟩; rfl
  right_inv := by rintro ⟨⟨parser,exporter⟩,rest⟩; rfl

def targetRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 2 9
def naturalRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 2 3
def countRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 8 3

def channelsLabel (point : Channels.Label) : Label := if point=.done then .target .boot else .channels point
def targetLabel (point : RawGetter.Label) : Label := if point=.done then .targetMove 0 else .target point
def targetMoveLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .count .boot else .targetMove point
def countLabel (point : RawNat.Label) : Label := if point=.done then .countMove 2 else .count point
def countMoveLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .build 0 else .countMove point
def buildLabel (point : RootB234.RuntimeCounter.Builder.Label) : Label := if point=5 then .clearCount else .build point
def roundLabel (point : RootB234.RuntimeCounter.Round.Label) : Label :=
  if point=7 then .done else if point=8 then .symbol .boot else .round point
def symbolLabel (point : RawNat.Label) : Label := if point=.done then .symbolMove 2 else .symbol point
def symbolMoveLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .round 0 else .symbolMove point

def capture (memory : Store C) (cell : Option Bool) : Store C :=
  (memory.1,((memory.2.1.1,(cell.isSome,cell.getD false)),memory.2.2))
def present (memory : Store C) : Bool := memory.2.1.2.1

/-- The original target, count and symbols are read in their original
order. The count is physically copied to a guarded counter, then erased
from3 before the symbol packets are accumulated there. All finite parser
registers are allocated at literal entry, before the original input. -/
noncomputable def program (caller : Statement C) : Label → Statement C
  | .channels point => LabelMap.statement channelsLabel (ContextLift.statement (Channels.program .halt point))
  | .target point => LabelMap.statement targetLabel (StoreIso.statement (rawIso C) (RawGetter.program .halt point))
  | .targetMove point => LabelMap.statement targetMoveLabel (StoreIso.statement (packetIso C)
      (RootB234.RatPacketTransport.atProgram targetRoles false point))
  | .count point => LabelMap.statement countLabel (StoreIso.statement (naturalIso C) (RawNat.program .halt point))
  | .countMove point => LabelMap.statement countMoveLabel (StoreIso.statement (packetIso C)
      (RootB234.RatPacketTransport.atProgram naturalRoles false point))
  | .build point => LabelMap.statement buildLabel (StoreIso.statement (packetIso C)
      (RootB234.RuntimeCounter.Builder.atProgram countRoles false point))
  | .clearCount => .pop 3 capture (.branch present (.goto (fun _ => .clearCount)) (.goto (fun _ => .round 0)))
  | .round point => LabelMap.statement roundLabel (StoreIso.statement (roundIso C) (RootB234.RuntimeCounter.Round.program point))
  | .symbol point => LabelMap.statement symbolLabel (StoreIso.statement (naturalIso C) (RawNat.program .halt point))
  | .symbolMove point => LabelMap.statement symbolMoveLabel (StoreIso.statement (packetIso C)
      (RootB234.RatPacketTransport.atProgram naturalRoles false point))
  | .done => caller

def channelsCfg (registers : NatAux) (before : Channels.State C) : State C :=
  LabelMap.configuration channelsLabel (ContextLift.configuration registers before)
def targetCfg (before : RawGetter.State (RawContext C)) : State C :=
  LabelMap.configuration targetLabel (StoreIso.configuration (rawIso C) before)
def targetMoveCfg (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration targetMoveLabel (StoreIso.configuration (packetIso C) before)
def countCfg (before : RawNat.State (Channels.Store C)) : State C :=
  LabelMap.configuration countLabel (StoreIso.configuration (naturalIso C) before)
def countMoveCfg (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration countMoveLabel (StoreIso.configuration (packetIso C) before)
def buildCfg (before : RootB234.RuntimeCounter.Builder.State (PacketContext C)) : State C :=
  LabelMap.configuration buildLabel (StoreIso.configuration (packetIso C) before)
def roundCfg (before : RootB234.RuntimeCounter.Round.State (RoundContext C)) : State C :=
  LabelMap.configuration roundLabel (StoreIso.configuration (roundIso C) before)
def symbolCfg (before : RawNat.State (Channels.Store C)) : State C :=
  LabelMap.configuration symbolLabel (StoreIso.configuration (naturalIso C) before)
def symbolMoveCfg (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration symbolMoveLabel (StoreIso.configuration (packetIso C) before)

def entry (context : C) (bits : List Bool) : State C := channelsCfg default (Channels.entry context bits)

theorem initial_default [Inhabited C] (bits : List Bool) :
    entry (default : C) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  rw [entry,Channels.initial_default]
  rfl

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end B23_4_RatWordPrep.WordFields
