module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsOriginal_089
public import RootB234_Cells_Public_003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordPack

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

abbrev Store (C : Type*) := WordFields.Store C
abbrev PacketContext (C : Type*) := WordFields.PacketContext C

inductive Label where
  | fields : WordFields.Label → Label
  | clear0 : RootB234.Cells.Label → Label
  | clear1 : RootB234.Cells.Label → Label
  | target : RootB234.RatPacketTransport.Label → Label
  | alphabet : RootB234.RatPacketTransport.Label → Label
  | wordCheck
  | wordMove : RootB234.RatPacketTransport.Label → Label
  | tableCheck
  | tableMove : RootB234.RatPacketTransport.Label → Label
  | reverse13 : RootB234.Cells.Label → Label
  | reverse3 : RootB234.Cells.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.fields default⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def targetRoles : RatInput.Stack ≃ RatInput.Stack := (Equiv.swap 15 9).trans (Equiv.swap 2 1)
def alphabetRoles : RatInput.Stack ≃ RatInput.Stack := (Equiv.swap 15 8).trans (Equiv.swap 2 1)
def wordRoles : RatInput.Stack ≃ RatInput.Stack := (Equiv.swap 15 3).trans (Equiv.swap 2 0)

def fieldsLabel (point : WordFields.Label) : Label := if point=.done then .clear0 0 else .fields point
def clear0Label (point : RootB234.Cells.Label) : Label := if point=6 then .clear1 0 else .clear0 point
def clear1Label (point : RootB234.Cells.Label) : Label := if point=6 then .target 0 else .clear1 point
def targetLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .alphabet 2 else .target point
def alphabetLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .wordCheck else .alphabet point
def wordLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .wordCheck else .wordMove point
def tableLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .tableCheck else .tableMove point
def reverse13Label (point : RootB234.Cells.Label) : Label := if point=4 then .reverse3 3 else .reverse13 point
def reverse3Label (point : RootB234.Cells.Label) : Label := if point=4 then .done else .reverse3 point

/-- Original-input data production followed by paid finite clear, static
packet routing and real EOF-driven queue reversal. Metadata1 holds N then
target, query0 and table2 regain original order, and arithmetic-owned8/9
and3/4/13 are physically empty before lookup/arithmetic begins. -/
noncomputable def program (caller : Statement C) : Label → Statement C
  | .fields point => LabelMap.statement fieldsLabel (WordFields.program .halt point)
  | .clear0 point => LabelMap.statement clear0Label (StoreIso.statement (WordFields.packetIso C)
      (RootB234.Cells.Public.clear0 point))
  | .clear1 point => LabelMap.statement clear1Label (StoreIso.statement (WordFields.packetIso C)
      (RootB234.Cells.Public.clear1 point))
  | .target point => LabelMap.statement targetLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RatPacketTransport.atProgram targetRoles false point))
  | .alphabet point => LabelMap.statement alphabetLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RatPacketTransport.atProgram alphabetRoles false point))
  | .wordCheck => .peek 3 WordFields.capture (.branch WordFields.present
      (.goto (fun _ => .wordMove 2)) (.goto (fun _ => .tableCheck)))
  | .wordMove point => LabelMap.statement wordLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RatPacketTransport.atProgram wordRoles false point))
  | .tableCheck => .peek 2 WordFields.capture (.branch WordFields.present
      (.goto (fun _ => .tableMove 0)) (.goto (fun _ => .reverse13 3)))
  | .tableMove point => LabelMap.statement tableLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RatPacketTransport.atProgram RootB234.RatPacketTransport.Public.copy2To13Roles false point))
  | .reverse13 point => LabelMap.statement reverse13Label (StoreIso.statement (WordFields.packetIso C)
      (RootB234.Cells.Public.reverse13To3 point))
  | .reverse3 point => LabelMap.statement reverse3Label (StoreIso.statement (WordFields.packetIso C)
      (RootB234.Cells.Public.reverse3To2 point))
  | .done => caller

def fieldsCfg (before : WordFields.State C) : State C := LabelMap.configuration fieldsLabel before
def packetCfg (rename : RootB234.RatPacketTransport.Label → Label)
    (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration rename (StoreIso.configuration (WordFields.packetIso C) before)
def cellsCfg (rename : RootB234.Cells.Label → Label)
    (before : RootB234.Cells.State (PacketContext C)) : State C :=
  LabelMap.configuration rename (StoreIso.configuration (WordFields.packetIso C) before)

def entry (context : C) (bits : List Bool) : State C := fieldsCfg (WordFields.entry context bits)

theorem initial_default [Inhabited C] (bits : List Bool) :
    entry (default : C) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  rw [entry,WordFields.initial_default]
  rfl

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end B23_4_RatWordPrep.WordPack
