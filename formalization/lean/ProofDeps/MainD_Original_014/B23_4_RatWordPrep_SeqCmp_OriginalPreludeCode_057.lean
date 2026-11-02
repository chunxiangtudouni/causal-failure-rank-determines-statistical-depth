module

public import B23_4_RatWordPrep_SeqCmp_RewindRun_056
public import B23_4_RatWordPrep_SeqCmp_OriginalFeeFrame_048

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalPrelude

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.PSTRWordVM

abbrev Store (C : Type*) := HeaderNat.Store (WholeCopy.Store (OriginalFee.Store C))
abbrev Extra := ((Bool × Bool) × PSTRSymbolicNaturalExport.Store) × Header.NativeMemory

inductive Label where
  | copy : WholeCopy.Label → Label
  | header : HeaderNat.Label → Label
  | rewind : Rewind.Label → Label
  | fee : OriginalFee.Label → Label
  | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.copy .boot⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def copyIso (C : Type*) : WholeCopy.Store (HeaderNat.Store (OriginalFee.Store C)) ≃ Store C where
  toFun := fun memory => (((memory.1.1.1,memory.2.1,memory.2.2),memory.1.1.2),memory.1.2)
  invFun := fun memory => (((memory.1.1.1,memory.1.2),memory.2),memory.1.1.2.1,memory.1.1.2.2)
  left_inv := by rintro ⟨⟨⟨base,natural⟩,native⟩,present,bit⟩; rfl
  right_inv := by rintro ⟨⟨⟨base,present,bit⟩,natural⟩,native⟩; rfl

def feeIso (C : Type*) : (Extra × OriginalFee.Store C) ≃ Store C where
  toFun := fun memory => (((memory.2,memory.1.1.1.1,memory.1.1.1.2),memory.1.1.2),memory.1.2)
  invFun := fun memory => ((((memory.1.1.2.1,memory.1.1.2.2),memory.1.2),memory.2),memory.1.1.1)
  left_inv := by rintro ⟨⟨⟨⟨present,bit⟩,natural⟩,native⟩,base⟩; rfl
  right_inv := by rintro ⟨⟨⟨base,present,bit⟩,natural⟩,native⟩; rfl

def extra (memory : Store C) : Extra := (((memory.1.1.2.1,memory.1.1.2.2),memory.1.2),memory.2)
def feeMemory (memory : Store C) : OriginalFee.Store C := memory.1.1.1

def rawMemory (context : C) : RawGetter.Store C := ((context,default),default)
def initialFeeMemory (context : C) : OriginalFee.Store C :=
  (OriginalFee.entry (rawMemory context) default default []).var

def copyLabel (point : WholeCopy.Label) : Label := if point=.done then .header default else .copy point
def headerLabel (point : HeaderNat.Label) : Label := if point=.done then .rewind default else .header point
def rewindLabel (point : Rewind.Label) : Label := if point=.done then .fee default else .rewind point
def feeLabel (point : OriginalFee.Label) : Label := if point=.done then .done else .fee point

/-- One source, with every finite auxiliary register allocated at entry.
Lookahead and rewind do not reset the original fee component's registers. -/
noncomputable def program (caller : Statement C) : Label → Statement C
  | .copy point => LabelMap.statement copyLabel (StoreIso.statement (copyIso C) (WholeCopy.program .halt point))
  | .header point => LabelMap.statement headerLabel (HeaderNat.program .halt point)
  | .rewind point => LabelMap.statement rewindLabel (StoreIso.statement (copyIso C) (Rewind.program .halt point))
  | .fee point => LabelMap.statement feeLabel (StoreIso.statement (feeIso C)
      (ContextLift.statement (OriginalFee.program .halt point)))
  | .done => caller

def copyCfg (before : WholeCopy.State (HeaderNat.Store (OriginalFee.Store C))) : State C :=
  LabelMap.configuration copyLabel (StoreIso.configuration (copyIso C) before)
def headerCfg (before : HeaderNat.State (WholeCopy.Store (OriginalFee.Store C))) : State C :=
  LabelMap.configuration headerLabel before
def rewindCfg (before : Rewind.State (HeaderNat.Store (OriginalFee.Store C))) : State C :=
  LabelMap.configuration rewindLabel (StoreIso.configuration (copyIso C) before)
def feeCfg (registers : Extra) (before : OriginalFee.State C) : State C :=
  LabelMap.configuration feeLabel (StoreIso.configuration (feeIso C) (ContextLift.configuration registers before))

def entry (context : C) (bits : List Bool) : State C :=
  ⟨some (.copy .boot),(((initialFeeMemory context,false,false),default),default),
    fun slot => if slot=0 then bits else []⟩

theorem feeMemory_entry (context : C) (bits : List Bool) :
    (OriginalFee.entry (rawMemory context) default default bits).var=initialFeeMemory context := rfl

theorem fee_split (memory : Store C) : feeIso C (extra memory,feeMemory memory)=memory := by
  rcases memory with ⟨⟨⟨base,present,bit⟩,natural⟩,native⟩
  rfl

theorem initial_default {C : Type*} [Inhabited C] (bits : List Bool) :
    entry (default : C) bits=TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 bits := by
  change (⟨some (default : Label),(default : Store C),_⟩ : State C)=⟨some default,default,_⟩
  congr 1
  funext slot
  fin_cases slot <;> rfl

private theorem supports_stmt {C : Type*} (body : Statement C) :
    TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports {C : Type*} : TM2.Supports (program (C := C) .halt) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end B23_4_RatWordPrep.OriginalPrelude
