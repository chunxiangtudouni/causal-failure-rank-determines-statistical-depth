module

public import RootB234_PrepExponent_QLoopPublic030

/-! Fixed full global-exponent control graph. All arithmetic and packet
programs are frozen callees. N, budget, Q, R, Y and E live on actual stacks;
none chooses source code, labels, finite control memory or support. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource

abbrev Stack := RatInput.Stack
abbrev Store (C : Type*) := QLoop.Store C

inductive MulSite where
  | twiceN | timesQ | firstY | nextY
  deriving DecidableEq

instance : Fintype MulSite where
  elems := {.twiceN,.timesQ,.firstY,.nextY}
  complete := by intro site;cases site <;> decide

inductive PacketSite where
  | copyQ | parkR | pullR | pullQ | copyBudget | restoreQ | restoreR | parkY
  | compareCopyY | compareParkY | compareCopyR | compareRestoreY
  | repeatCopyY | repeatDiscardY | repeatParkY
  | stopDropY | stopDropR | stopPullQ | stopCopyBudget | stopRestoreQ
  deriving DecidableEq

instance : Fintype PacketSite where
  elems := {.copyQ,.parkR,.pullR,.pullQ,.copyBudget,.restoreQ,.restoreR,.parkY,
    .compareCopyY,.compareParkY,.compareCopyR,.compareRestoreY,.repeatCopyY,.repeatDiscardY,.repeatParkY,
    .stopDropY,.stopDropR,.stopPullQ,.stopCopyBudget,.stopRestoreQ}
  complete := by intro site;cases site <;> decide

inductive ClearSite where
  | repeatY | stopY | stopR
  deriving DecidableEq

instance : Fintype ClearSite where
  elems := {.repeatY,.stopY,.stopR}
  complete := by intro site;cases site <;> decide

inductive Label where
  | q : QLoop.Label → Label
  | packet : PacketSite → RatPacketTransport.Label → Label
  | nat : NatToRat.Label → Label
  | literal : MulSite → Label
  | mul : MulSite → RatBinary.Label → Label
  | seedE
  | subtract : RatBinary.Label → Label
  | reader : RatCmp.Reader.Label → Label
  | branch
  | clear : ClearSite → Cells.Label → Label
  | increment : NatIncrement.Label → Label
  | done
  deriving DecidableEq,Fintype

instance : Inhabited Label := ⟨.q default⟩
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)
variable {C : Type*}

def packetRoles : PacketSite → Stack ≃ Stack
  | .copyQ | .copyBudget | .compareCopyY | .compareCopyR | .repeatCopyY | .stopCopyBudget => QLoop.copyRoles
  | .parkR | .parkY | .repeatParkY => QLoop.parkRoles
  | .pullR | .compareParkY | .repeatDiscardY | .stopDropY | .stopDropR | .stopPullQ => QLoop.discardRoles
  | .pullQ => ((Equiv.swap 15 7).trans (Equiv.swap 2 13)).trans (Equiv.swap 4 3)
  | .restoreQ => ((Equiv.swap 15 13).trans (Equiv.swap 2 7)).trans (Equiv.swap 4 3)
  | .restoreR | .compareRestoreY | .stopRestoreQ =>
      ((Equiv.swap 15 12).trans (Equiv.swap 2 7)).trans (Equiv.swap 4 3)

def packetCopy : PacketSite → Bool
  | .copyQ | .copyBudget | .compareCopyY | .compareCopyR | .repeatCopyY | .stopCopyBudget => true
  | _ => false

def packetNext : PacketSite → Label
  | .copyQ => .nat default
  | .parkR => .packet .pullR 0
  | .pullR => .packet .pullQ 0
  | .pullQ => .packet .copyBudget 0
  | .copyBudget => .packet .restoreQ 0
  | .restoreQ => .packet .restoreR 0
  | .restoreR => .literal .firstY
  | .parkY => .seedE
  | .compareCopyY => .packet .compareParkY 0
  | .compareParkY => .packet .compareCopyR 0
  | .compareCopyR => .packet .compareRestoreY 0
  | .compareRestoreY => .subtract default
  | .repeatCopyY => .literal .nextY
  | .repeatDiscardY => .clear .repeatY 0
  | .repeatParkY => .increment 0
  | .stopDropY => .clear .stopY 0
  | .stopDropR => .clear .stopR 0
  | .stopPullQ => .packet .stopCopyBudget 0
  | .stopCopyBudget => .packet .stopRestoreQ 0
  | .stopRestoreQ => .done

def mulNext : MulSite → Label
  | .twiceN => .mul .timesQ default
  | .timesQ => .packet .parkR 0
  | .firstY => .packet .parkY 0
  | .nextY => .packet .repeatDiscardY 0

def clearNext : ClearSite → Label
  | .repeatY => .packet .repeatParkY 0
  | .stopY => .packet .stopDropR 0
  | .stopR => .packet .stopPullQ 0

def qLabel (point : QLoop.Label) : Label := if point=.done then .packet .copyQ 0 else .q point
def packetLabel (site : PacketSite) (point : RatPacketTransport.Label) : Label :=
  if point=4 then packetNext site else .packet site point
def natLabel (point : NatToRat.Label) : Label := if point=.done then .literal .twiceN else .nat point
def mulLabel (site : MulSite) (point : RatBinary.Label) : Label := if point=.done then mulNext site else .mul site point
def subLabel (point : RatBinary.Label) : Label := if point=.done then .reader 0 else .subtract point
def readerLabel (point : RatCmp.Reader.Label) : Label := if point=4 then .branch else .reader point
def clearLabel (site : ClearSite) (point : Cells.Label) : Label := if point=6 then clearNext site else .clear site point
def incrementLabel (point : NatIncrement.Label) : Label :=
  if point=4 then .packet .compareCopyY 0 else .increment point

def readerIso (C : Type*) :
    (Arithmetic.ReaderContext (PacketUnary.Store C)×RatCmp.Reader.Store) ≃ Store C :=
  (Arithmetic.readerIso (PacketUnary.Store C)).trans (QLoop.arithmeticIso C)

def prepend (slot : Stack) : List Bool → Statement C → Statement C
  | [],tail => tail
  | bit::later,tail => prepend slot later (.push slot (fun _ => bit) tail)

def program (caller : Statement C) : Label → Statement C
  | .q point => LabelMap.statement qLabel (QLoop.program .halt point)
  | .packet site point => LabelMap.statement (packetLabel site)
      (RatPacketTransport.atProgram (packetRoles site) (packetCopy site) point)
  | .nat point => LabelMap.statement natLabel (NatToRat.program .halt point)
  | .literal site => prepend 15 (RatInput.Encoder.packet (2 : Rat) []) (.goto (fun _ => .mul site default))
  | .mul site point => LabelMap.statement (mulLabel site)
      (StoreIso.statement (QLoop.arithmeticIso C) (Arithmetic.mulProgram point))
  | .seedE => prepend 11 (B23_4_RatWordPrep.NatField.packet 1 []) (.goto (fun _ => .packet .compareCopyY 0))
  | .subtract point => LabelMap.statement subLabel
      (StoreIso.statement (QLoop.arithmeticIso C) (Arithmetic.subProgram point))
  | .reader point => LabelMap.statement readerLabel
      (StoreIso.statement (readerIso C) (RatCmp.Reader.program .halt point))
  | .branch => .pop 3 QLoop.capture (.branch (fun memory => memory.2.2)
      (.goto (fun _ => .packet .stopDropY 0)) (.goto (fun _ => .packet .repeatCopyY 0)))
  | .clear site point => LabelMap.statement (clearLabel site)
      (StackIso.statement QLoop.clearRoles (Cells.Public.clear0 point))
  | .increment point => LabelMap.statement incrementLabel (NatIncrement.program .halt point)
  | .done => caller

theorem prepend_step (slot : Stack) (cells : List Bool) (next : Statement C)
    (memory : Store C) (before : Stack → List Bool) :
    TM2.stepAux (prepend slot cells next) memory before=
      TM2.stepAux next memory (Function.update before slot (cells++before slot)) := by
  induction cells generalizing next with
  | nil => simp only [prepend,List.nil_append,Function.update_eq_self]
  | cons bit later ih =>
    rw [prepend,ih]
    simp only [TM2.stepAux,Function.update_self,Function.update_idem,List.cons_append]

private theorem supports_stmt (body : Statement C) :
    TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _;exact Finset.mem_univ _
  | halt => trivial

theorem supports (caller : Statement C) : TM2.Supports (program caller) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => supports_stmt (program caller point)⟩

theorem finite_store [Finite C] : Finite (Store C) := QLoop.finite_store

end RootB234.PrepExponent.Global
