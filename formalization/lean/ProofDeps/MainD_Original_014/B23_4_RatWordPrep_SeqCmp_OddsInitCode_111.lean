module

public import B23_4_RatWordPrep_SeqCmp_FullStore_110
public import B23_4_RatWordPrep_SeqCmp_WordPackOriginal_109

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.OddsInit

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

abbrev Store (C : Type*) := FullStore.Store C
abbrev PacketContext (C : Type*) := FullStore.Aux × WordFields.PacketContext C

inductive Label where
  | prep : WordPack.Label → Label
  | fee : RootB234.RatPacketTransport.Label → Label
  | erase : RootB234.Cells.Label → Label
  | parkComp : RootB234.RatPacketTransport.Label → Label
  | parkPrior : RootB234.RatPacketTransport.Label → Label
  | returnComp : RootB234.RatPacketTransport.Label → Label
  | returnPrior : RootB234.RatPacketTransport.Label → Label
  | divide : RatBinary.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.prep default⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

instance storeInhabited [Inhabited C] : Inhabited (Store C) :=
  ⟨((default : FullStore.Aux),(default : WordPack.Store C))⟩

def packetIso (C : Type*) : RootB234.RatPacketTransport.Store (PacketContext C) ≃ Store C where
  toFun := fun v => (v.1.1,WordFields.packetIso C (v.1.2,v.2))
  invFun := fun v => let old := (WordFields.packetIso C).symm v.2
    ((v.1,old.1),old.2)
  left_inv := by rintro ⟨⟨aux,rest⟩,flags⟩; rfl
  right_inv := by rintro ⟨aux,rest⟩; rfl

def feeRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 2 13
def priorRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 2 14
def compReturnRoles : RatInput.Stack ≃ RatInput.Stack := (Equiv.swap 15 13).trans (Equiv.swap 2 15)
def priorReturnRoles : RatInput.Stack ≃ RatInput.Stack := (Equiv.swap 15 14).trans (Equiv.swap 2 15)
def eraseRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 0 13

def prepLabel (point : WordPack.Label) : Label := if point=.done then .fee 0 else .prep point
def feeLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .erase 0 else .fee point
def eraseLabel (point : RootB234.Cells.Label) : Label := if point=6 then .parkComp 0 else .erase point
def compLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .parkPrior 0 else .parkComp point
def priorLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .returnComp 0 else .parkPrior point
def compReturnLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .returnPrior 0 else .returnComp point
def priorReturnLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .divide default else .returnPrior point
def divideLabel (point : RatBinary.Label) : Label := if point=.done then .done else .divide point

/-- Literal original input to paid prior-odds initialization. Fee is
physically moved and cleared, prior/complement are physically swapped,
and the frozen division instruction produces the initial odds. All
division/multiplication/subtraction/output auxiliaries exist at entry. -/
noncomputable def program (caller : Statement C) : Label → Statement C
  | .prep point => LabelMap.statement prepLabel (ContextLift.statement (WordPack.program .halt point))
  | .fee point => LabelMap.statement feeLabel (StoreIso.statement (packetIso C)
      (RootB234.RatPacketTransport.atProgram feeRoles false point))
  | .erase point => LabelMap.statement eraseLabel (StoreIso.statement (packetIso C)
      (StackIso.statement eraseRoles (RootB234.Cells.Public.clear0 point)))
  | .parkComp point => LabelMap.statement compLabel (StoreIso.statement (packetIso C)
      (RootB234.RatPacketTransport.atProgram feeRoles false point))
  | .parkPrior point => LabelMap.statement priorLabel (StoreIso.statement (packetIso C)
      (RootB234.RatPacketTransport.atProgram priorRoles false point))
  | .returnComp point => LabelMap.statement compReturnLabel (StoreIso.statement (packetIso C)
      (RootB234.RatPacketTransport.atProgram compReturnRoles false point))
  | .returnPrior point => LabelMap.statement priorReturnLabel (StoreIso.statement (packetIso C)
      (RootB234.RatPacketTransport.atProgram priorReturnRoles false point))
  | .divide point => LabelMap.statement divideLabel (StoreIso.statement (FullStore.divIso C)
      (RatBinary.program RatMulDiv.divSource .halt point))
  | .done => caller

def prepCfg (registers : FullStore.Aux) (before : WordPack.State C) : State C :=
  LabelMap.configuration prepLabel (ContextLift.configuration registers before)
def packetCfg (rename : RootB234.RatPacketTransport.Label → Label)
    (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration rename (StoreIso.configuration (packetIso C) before)
def eraseCfg (before : RootB234.Cells.State (PacketContext C)) : State C :=
  LabelMap.configuration eraseLabel (StoreIso.configuration (packetIso C) before)
def divideCfg (before : RatBinary.State (FullStore.DivContext C) RatMulDiv.divStates) : State C :=
  LabelMap.configuration divideLabel (StoreIso.configuration (FullStore.divIso C) before)

def entry (context : C) (bits : List Bool) : State C := prepCfg default (WordPack.entry context bits)

theorem initial_default [Inhabited C] (bits : List Bool) :
    entry (default : C) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  rw [entry,WordPack.initial_default]
  rfl

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end B23_4_RatWordPrep.OddsInit
