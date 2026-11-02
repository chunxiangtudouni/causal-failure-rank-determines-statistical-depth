module

public import B23_4_RatWordPrep_SeqCmp_WordFoldOriginal_125
public import RootB234_WordFinalizer_Public_004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

abbrev Store (C : Type*) := FullStore.Store C
abbrev PacketContext (C : Type*) := OddsInit.PacketContext C

inductive Job where
  | targetForSub | parkComplement | targetForHigh | complementForHigh | parkHigh
  | complementForLow | targetForLow | parkLow | cacheOdds | oddsFirst | oddsMiddle
  | high | low | oddsLast
  deriving DecidableEq

instance : Fintype Job where
  elems := {.targetForSub,.parkComplement,.targetForHigh,.complementForHigh,.parkHigh,
    .complementForLow,.targetForLow,.parkLow,.cacheOdds,.oddsFirst,.oddsMiddle,.high,.low,.oddsLast}
  complete := by intro job; cases job <;> simp

inductive OneJob where
  | complement | map
  deriving DecidableEq

instance : Fintype OneJob where
  elems := {.complement,.map}
  complete := by intro job; cases job <;> simp

inductive Label where
  | fold : WordFold.Label → Label
  | metadata : RootB234.RatPacketTransport.Label → Label
  | clear : RootB234.Cells.Label → Label
  | packet : Job → RootB234.RatPacketTransport.Label → Label
  | one : OneJob → Label
  | subtract : RatBinary.Label → Label
  | divide : Bool → RatBinary.Label → Label
  | word : SeqCmp.Word.Label → Label
  | finalize : RootB234.WordFinalizer.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.fold default⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def source : Job → RatInput.Stack
  | .targetForSub | .targetForHigh | .targetForLow | .oddsFirst | .oddsMiddle | .oddsLast => 1
  | .complementForHigh | .complementForLow | .low => 0
  | .high => 2
  | .parkComplement | .parkHigh | .parkLow | .cacheOdds => 15

def destination : Job → RatInput.Stack
  | .parkComplement | .parkLow => 0
  | .parkHigh => 2
  | .cacheOdds => 1
  | _ => 15

def copy : Job → Bool
  | .parkComplement | .parkHigh | .parkLow => false
  | _ => true

def roles (job : Job) : RatInput.Stack ≃ RatInput.Stack :=
  (Equiv.swap 15 (source job)).trans (Equiv.swap ((Equiv.swap 15 (source job)) 2) (destination job))

def metadataRoles : RatInput.Stack ≃ RatInput.Stack := (Equiv.swap 15 1).trans (Equiv.swap 2 0)

def next : Job → Label
  | .targetForSub => .one .complement
  | .parkComplement => .packet .targetForHigh 0
  | .targetForHigh => .packet .complementForHigh 0
  | .complementForHigh => .divide true default
  | .parkHigh => .packet .complementForLow 0
  | .complementForLow => .packet .targetForLow 0
  | .targetForLow => .divide false default
  | .parkLow => .packet .cacheOdds 0
  | .cacheOdds => .packet .oddsFirst 0
  | .oddsFirst => .one .map
  | .oddsMiddle => .packet .high 0
  | .high => .packet .low 0
  | .low => .packet .oddsLast 0
  | .oddsLast => .word default

def foldLabel (point : WordFold.Label) : Label := if point=.done then .metadata 2 else .fold point
def metadataLabel (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then .clear 0 else .metadata point
def clearLabel (point : RootB234.Cells.Label) : Label := if point=6 then .packet .targetForSub 0 else .clear point
def packetLabel (job : Job) (point : RootB234.RatPacketTransport.Label) : Label := if point=4 then next job else .packet job point
def subLabel (point : RatBinary.Label) : Label := if point=.done then .packet .parkComplement 0 else .subtract point
def divLabel (high : Bool) (point : RatBinary.Label) : Label :=
  if point=.done then .packet (if high then .parkHigh else .parkLow) 0 else .divide high point
def wordLabel (point : SeqCmp.Word.Label) : Label := if point=.done then .finalize .clear else .word point
def finalLabel (point : RootB234.WordFinalizer.Label) : Label := .finalize point

def oneNext : OneJob → Label
  | .complement => .subtract default
  | .map => .packet .oddsMiddle 0

/-- Fixed constant bits only. No experiment, target, odds, or computed
answer is encoded in the source; all nonconstant packets are transported. -/
def pushCells : List Bool → Statement C → Statement C
  | [], body => body
  | bit::bits, body => pushCells bits (.push 15 (fun _ => bit) body)

noncomputable def program (caller : Statement C) : Label → Statement C
  | .fold point => LabelMap.statement foldLabel (WordFold.program .halt point)
  | .metadata point => LabelMap.statement metadataLabel (StoreIso.statement (OddsInit.packetIso C)
      (RootB234.RatPacketTransport.atProgram metadataRoles false point))
  | .clear point => LabelMap.statement clearLabel (StoreIso.statement (OddsInit.packetIso C)
      (RootB234.Cells.Public.clear0 point))
  | .packet job point => LabelMap.statement (packetLabel job) (StoreIso.statement (OddsInit.packetIso C)
      (RootB234.RatPacketTransport.atProgram (roles job) (copy job) point))
  | .one job => pushCells (RatInput.Encoder.packet (1:Rat) []) (.goto (fun _ => oneNext job))
  | .subtract point => LabelMap.statement subLabel (StoreIso.statement (FullStore.subIso C)
      (RatBinary.program RatAddSub.subSource .halt point))
  | .divide high point => LabelMap.statement (divLabel high) (StoreIso.statement (FullStore.divIso C)
      (RatBinary.program RatMulDiv.divSource .halt point))
  | .word point => LabelMap.statement wordLabel (StoreIso.statement (FullStore.wordIso C)
      (SeqCmp.Word.program .halt point))
  | .finalize point => LabelMap.statement finalLabel (StoreIso.statement (OddsInit.packetIso C)
      (RootB234.WordFinalizer.program point))
  | .done => caller

def foldCfg (before : WordFold.State C) : State C := LabelMap.configuration foldLabel before
def entry (context : C) (bits : List Bool) : State C := foldCfg (WordFold.entry context bits)

theorem initial_default [Inhabited C] (bits : List Bool) :
    entry (default : C) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  rw [entry,WordFold.initial_default]
  rfl

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

theorem roles_source (job : Job) : roles job 15=source job := by cases job <;> rfl
theorem roles_destination (job : Job) : roles job 2=destination job := by cases job <;> rfl
theorem roles_scratch (job : Job) : roles job 4=4 := by cases job <;> rfl

end B23_4_RatWordPrep.WordFinish
