module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsOriginal_089

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

abbrev Store (C : Type*) := WordFields.Store C
abbrev PacketContext (C : Type*) := WordFields.PacketContext C
abbrev RoundContext (C : Type*) := WordFields.RoundContext C

inductive Label where
  | boot
  | buildN : RootB234.RuntimeCounter.Builder.Label → Label
  | roundN : RootB234.RuntimeCounter.Round.Label → Label
  | moveN : RootB234.RatPacketTransport.Label → Label
  | buildJ : RootB234.RuntimeCounter.Builder.Label → Label
  | roundJ : RootB234.RuntimeCounter.Round.Label → Label
  | moveJ : RootB234.RatPacketTransport.Label → Label
  | copy : RootB234.RatPacketTransport.Label → Label
  | restore
  | restoreMove : RootB234.RatPacketTransport.Label → Label
  | unmark
  | selected : RootB234.RatPacketTransport.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.boot⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def sourceNRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 8 1
def sourceJRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 8 0
def missRoles : RatInput.Stack ≃ RatInput.Stack := Equiv.swap 15 2
def bit (memory : Store C) : Bool := memory.2.1.2.2

def buildNLabel (point : RootB234.RuntimeCounter.Builder.Label) : Label := if point=5 then .roundN 0 else .buildN point
def buildJLabel (point : RootB234.RuntimeCounter.Builder.Label) : Label := if point=5 then .roundJ 0 else .buildJ point
def roundNLabel (point : RootB234.RuntimeCounter.Round.Label) : Label :=
  if point=7 then .buildJ 0 else if point=8 then .moveN 0 else .roundN point
def roundJLabel (point : RootB234.RuntimeCounter.Round.Label) : Label :=
  if point=7 then .copy 0 else if point=8 then .moveJ 0 else .roundJ point
def moveNLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .roundN 0 else .moveN point
def moveJLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .roundJ 0 else .moveJ point
def copyLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .restore else .copy point
def restoreLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .restore else .restoreMove point
def selectedLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .done else .selected point

/-- A fixed positional lookup. False skips actual j fields; true skips
actual N fields then j. Both counts are copied from physical natural
packets. Real positive rounds move a table packet above an owned FALSE
marker; zero copies the selected real packet. The archive is restored
before returning the selected packet above the original odds bank. -/
noncomputable def program (truth : Bool) (caller : Statement C) : Label → Statement C
  | .boot => .push 15 (fun _ => false) (.goto (fun _ => if truth then .buildN 0 else .buildJ 0))
  | .buildN point => LabelMap.statement buildNLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RuntimeCounter.Builder.atProgram sourceNRoles false point))
  | .buildJ point => LabelMap.statement buildJLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RuntimeCounter.Builder.atProgram sourceJRoles false point))
  | .roundN point => LabelMap.statement roundNLabel (StoreIso.statement (WordFields.roundIso C)
      (RootB234.RuntimeCounter.Round.program point))
  | .roundJ point => LabelMap.statement roundJLabel (StoreIso.statement (WordFields.roundIso C)
      (RootB234.RuntimeCounter.Round.program point))
  | .moveN point => LabelMap.statement moveNLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RatPacketTransport.atProgram missRoles false point))
  | .moveJ point => LabelMap.statement moveJLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RatPacketTransport.atProgram missRoles false point))
  | .copy point => LabelMap.statement copyLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RatPacketTransport.Public.copy2To13 point))
  | .restore => .peek 15 WordFields.capture (.branch bit
      (.goto (fun _ => .restoreMove 0)) (.goto (fun _ => .unmark)))
  | .restoreMove point => LabelMap.statement restoreLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RatPacketTransport.Public.move15To2 point))
  | .unmark => .pop 15 WordFields.capture (.goto (fun _ => .selected 0))
  | .selected point => LabelMap.statement selectedLabel (StoreIso.statement (WordFields.packetIso C)
      (RootB234.RatPacketTransport.Public.move13To15 point))
  | .done => caller

def entry (memory : Store C) (bank : RatInput.Stack → List Bool) : State C := ⟨some .boot,memory,bank⟩

def packetCfg (rename : RootB234.RatPacketTransport.Label → Label)
    (before : RootB234.RatPacketTransport.State (PacketContext C)) : State C :=
  LabelMap.configuration rename (StoreIso.configuration (WordFields.packetIso C) before)
def builderCfg (rename : RootB234.RuntimeCounter.Builder.Label → Label)
    (before : RootB234.RuntimeCounter.Builder.State (PacketContext C)) : State C :=
  LabelMap.configuration rename (StoreIso.configuration (WordFields.packetIso C) before)
def roundCfg (rename : RootB234.RuntimeCounter.Round.Label → Label)
    (before : RootB234.RuntimeCounter.Round.State (RoundContext C)) : State C :=
  LabelMap.configuration rename (StoreIso.configuration (WordFields.roundIso C) before)

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports (truth : Bool) : TM2.Supports (program (C := C) truth .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end B23_4_RatWordPrep.Lookup
