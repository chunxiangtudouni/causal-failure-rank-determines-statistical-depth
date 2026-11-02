module

public import Paid.PDROC_BitVM_Kernel_RatInstruction_048
public import Paid.PDROC_BitVM_Kernel_CompareFlag_049
public import Paid.PDROC_BitVM_Kernel_BoolCell_044

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RatCompare

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

def LocalLabel (index : Fin 4) : Type :=
  if index=0 then RawInstruction.Label else if index=1 then Unit else if index=2 then Unit else RawWrite.Label

def LocalStore (states : ℕ) (index : Fin 4) : Type :=
  if index=0 then RawInstruction.Store states else if index=1 then Branch.Store
  else if index=2 then Bool else RawWrite.Store

instance labelFintype (index : Fin 4) : Fintype (LocalLabel index) := by
  unfold LocalLabel
  split_ifs <;> infer_instance

instance labelInhabited (index : Fin 4) : Inhabited (LocalLabel index) := by
  unfold LocalLabel
  split_ifs <;> infer_instance

instance storeFintype (states : ℕ) (index : Fin 4) : Fintype (LocalStore states index) := by
  unfold LocalStore
  split_ifs <;> infer_instance

def startLabel (index : Fin 4) : LocalLabel index :=
  if h0 : index=0 then by
    subst index
    exact CallFamily.labels RawInstruction.LocalLabel 0 (RawInstruction.startLabel 0)
  else if h1 : index=1 then by subst index; exact ()
  else if h2 : index=2 then by subst index; exact ()
  else by
    have h3 : index=3 := by fin_cases index <;> simp_all
    subst index
    exact RawWrite.clearLabel 0

def initialStore (states : ℕ) (index : Fin 4) : LocalStore states index :=
  if h0 : index=0 then by subst index; exact RawInstruction.initialized states
  else if h1 : index=1 then by subst index; exact (default : Branch.Store)
  else if h2 : index=2 then by subst index; exact false
  else by
    have h3 : index=3 := by fin_cases index <;> simp_all
    subst index
    exact (RawWrite.before (fun _=>[]) default).var

def source {states : ℕ} (machine : Machine states) (target left right : Register) (index : Fin 4) :
    LocalLabel index → TM2.Stmt Alphabet (LocalLabel index) (LocalStore states index) :=
  if h0 : index=0 then by subst index; exact RawInstruction.program machine target left right
  else if h1 : index=1 then by subst index; exact Branch.program (registerSlot target)
  else if h2 : index=2 then by subst index; exact BoolCell.program
  else by
    have h3 : index=3 := by fin_cases index <;> simp_all
    subst index
    exact RawWrite.program target

abbrev Label := CallFamily.Label LocalLabel
abbrev Store (states : ℕ) := CallFamily.Store (LocalStore states)
abbrev State (states : ℕ) := TM2.Cfg Alphabet Label (Store states)

def initialized (states : ℕ) : Store states := initialStore states
instance storeInhabited (states : ℕ) : Inhabited (Store states) := ⟨initialized states⟩

def entry (states : ℕ) (index : Fin 4) : TM2.Stmt Alphabet Label (Store states) :=
  .load (fun store=>Function.update store index (initialStore states index))
    (.goto (fun _=>CallFamily.labels LocalLabel index (startLabel index)))

/-- The comparison decision is computed from the actual captured finite
flags, then stored by a REAL caller load before the four literal writes.
No rational value or mathematical order test is a transition argument. -/
def observedEntry (states : ℕ) (comparison : Comparison) : TM2.Stmt Alphabet Label (Store states) :=
  .load (fun store=>Function.update store (2 : Fin 4) (CompareFlag.flag comparison (store 1)))
    (.goto (fun _=>CallFamily.labels LocalLabel 2 (startLabel 2)))

def resume (states : ℕ) (comparison : Comparison) (index : Fin 4) : TM2.Stmt Alphabet Label (Store states) :=
  if index=0 then entry states 1 else if index=1 then observedEntry states comparison
  else if index=2 then entry states 3 else .halt

/-- Fixed four-phase code: complete actual RAW difference into target,
real five-prefix inspection there, actual Bool Cell creation on work0,
and complete actual canonical target replacement/cleanup. All operands
were copied before target changed, so arbitrary source aliases are safe. -/
def program {states : ℕ} (machine : Machine states) (comparison : Comparison) (target left right : Register) :
    Label → TM2.Stmt Alphabet Label (Store states) :=
  CallFamily.machine LocalLabel (LocalStore states) (source machine target left right) (resume states comparison)

def before (states : ℕ) (contents : Stack → List Bool) : State states :=
  ⟨some (CallFamily.labels LocalLabel 0 (startLabel 0)),initialized states,contents⟩

theorem source_supports {states : ℕ} (machine : Machine states) (target left right : Register) (index : Fin 4) :
    TM2.Supports (source machine target left right index) (Finset.univ : Finset (LocalLabel index)) := by
  fin_cases index
  · exact RawInstruction.supports machine target left right
  · exact Branch.supports (registerSlot target)
  · exact BoolCell.supports
  · exact RawWrite.supports target

theorem supports {states : ℕ} (machine : Machine states) (comparison : Comparison) (target left right : Register) :
    TM2.Supports (program machine comparison target left right) (Finset.univ : Finset Label) := by
  apply CallFamily.supports
  · intro index
    exact source_supports machine target left right index
  · intro index
    fin_cases index <;> simp [resume,entry,observedEntry,TM2.SupportsStmt]

end PDROC.BitVM.Kernel.RatCompare
