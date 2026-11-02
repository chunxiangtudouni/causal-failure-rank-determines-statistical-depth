module

public import B23_4_RatWordPrep_SeqCmp_OriginalPreludePublic_066
public import B23_4_RatWordPrep_SeqCmp_RawNatPublic_075
public import RootB234_RuntimeCounter_Builder_Public005
public import RootB234_RuntimeCounter_Round_Public_007
public import RootB234_RatPacketTransport_Public005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Channels

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

abbrev RawAux := RawGetter.ParserMemory × PSTRSymbolicNaturalExport.Store
abbrev Aux := (RawAux × RootB234.RuntimeCounter.Round.Registers) × RatOutput.Store
abbrev Store (C : Type*) := Aux × OriginalPrelude.Store C
abbrev RawContext (C : Type*) :=
  (RootB234.RuntimeCounter.Round.Registers × RatOutput.Store) × OriginalPrelude.Store C
abbrev RoundContext (C : Type*) := (RawAux × RatOutput.Store) × OriginalPrelude.Store C
abbrev PacketContext (C : Type*) := (RawAux × RootB234.RuntimeCounter.Round.Registers) × OriginalPrelude.Store C

inductive Label where
  | prelude : OriginalPrelude.Label → Label
  | build : RootB234.RuntimeCounter.Builder.Label → Label
  | round : RootB234.RuntimeCounter.Round.Label → Label
  | read : RawGetter.Label → Label
  | move : RootB234.RatPacketTransport.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.prelude default⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def rawIso (C : Type*) : RawGetter.Store (RawContext C) ≃ Store C where
  toFun := fun v => ((((v.1.2,v.2),v.1.1.1.1),v.1.1.1.2),v.1.1.2)
  invFun := fun v => ((((v.1.1.2,v.1.2),v.2),v.1.1.1.1),v.1.1.1.2)
  left_inv := by rintro ⟨⟨⟨⟨roundMemory,packetMemory⟩,base⟩,parser⟩,natural⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨parser,natural⟩,roundMemory⟩,packetMemory⟩,base⟩; rfl

def roundIso (C : Type*) : RootB234.RuntimeCounter.Round.Store (RoundContext C) ≃ Store C where
  toFun := fun v => (((v.1.1.1,v.2),v.1.1.2),v.1.2)
  invFun := fun v => (((v.1.1.1,v.1.2),v.2),v.1.1.2)
  left_inv := by rintro ⟨⟨⟨raw,packetMemory⟩,base⟩,roundMemory⟩; rfl
  right_inv := by rintro ⟨⟨⟨raw,roundMemory⟩,packetMemory⟩,base⟩; rfl

def packetIso (C : Type*) : RootB234.RatPacketTransport.Store (PacketContext C) ≃ Store C :=
  StoreIso.exchange (RawAux × RootB234.RuntimeCounter.Round.Registers) (OriginalPrelude.Store C) RatOutput.Store

def preludeLabel (point : OriginalPrelude.Label) : Label := if point=.done then .build 0 else .prelude point
def buildLabel (point : RootB234.RuntimeCounter.Builder.Label) : Label := if point=5 then .round 0 else .build point
def roundLabel (point : RootB234.RuntimeCounter.Round.Label) : Label :=
  if point=7 then .done else if point=8 then .read .boot else .round point
def readLabel (point : RawGetter.Label) : Label := if point=.done then .move 0 else .read point
def moveLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .round 0 else .move point

/-- All finite registers exist at literal entry. The positive counter
port reads one actual rational field, physically moves its packet to2,
then returns to the same real counter source. No N/width/fuel is code. -/
noncomputable def program (caller : Statement C) : Label → Statement C
  | .prelude point => LabelMap.statement preludeLabel (ContextLift.statement (OriginalPrelude.program .halt point))
  | .build point => LabelMap.statement buildLabel (StoreIso.statement (packetIso C)
      (RootB234.RuntimeCounter.Builder.Public.from8Twice point))
  | .round point => LabelMap.statement roundLabel (StoreIso.statement (roundIso C)
      (RootB234.RuntimeCounter.Round.program point))
  | .read point => LabelMap.statement readLabel (StoreIso.statement (rawIso C) (RawGetter.program .halt point))
  | .move point => LabelMap.statement moveLabel (StoreIso.statement (packetIso C)
      (RootB234.RatPacketTransport.Public.move15To2 point))
  | .done => caller

def preludeCfg (registers : Aux) (before : OriginalPrelude.State C) : State C :=
  LabelMap.configuration preludeLabel (ContextLift.configuration registers before)
def buildCfg (before : RootB234.RuntimeCounter.Builder.State (PacketContext C)) : State C :=
  LabelMap.configuration buildLabel (StoreIso.configuration (packetIso C) before)
def roundCfg (before : RootB234.RuntimeCounter.Round.State (RoundContext C)) : State C :=
  LabelMap.configuration roundLabel (StoreIso.configuration (roundIso C) before)
def readCfg (before : RawGetter.State (RawContext C)) : State C :=
  LabelMap.configuration readLabel (StoreIso.configuration (rawIso C) before)
def moveCfg (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration moveLabel (StoreIso.configuration (packetIso C) before)

def entry (context : C) (bits : List Bool) : State C := preludeCfg default (OriginalPrelude.entry context bits)

theorem initial_default [Inhabited C] (bits : List Bool) :
    entry (default : C) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  rw [entry,OriginalPrelude.initial_default]
  rfl

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end B23_4_RatWordPrep.Channels
