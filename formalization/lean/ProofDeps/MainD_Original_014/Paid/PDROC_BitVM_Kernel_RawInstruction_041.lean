module

public import Paid.PDROC_BitVM_Kernel_RawCompute_034
public import Paid.PDROC_BitVM_Kernel_RawResult_031
public import Paid.PDROC_BitVM_Kernel_RawWriter_040
public import Paid.PDROC_BitVM_Kernel_CallFamily_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawInstruction

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.PSTRWordBool

def LocalLabel (index : Fin 3) : Type :=
  if index=0 then RawOp.Label else if index=1 then Unit else RawWrite.Label

def LocalStore (states : ℕ) (index : Fin 3) : Type :=
  if index=0 then RawOp.Store states else if index=1 then Unit else RawWrite.Store

instance labelFintype (index : Fin 3) : Fintype (LocalLabel index) := by
  unfold LocalLabel
  split_ifs <;> infer_instance

instance labelInhabited (index : Fin 3) : Inhabited (LocalLabel index) := by
  unfold LocalLabel
  split_ifs <;> infer_instance

instance storeFintype (states : ℕ) (index : Fin 3) : Fintype (LocalStore states index) := by
  unfold LocalStore
  split_ifs <;> infer_instance

def startLabel (index : Fin 3) : LocalLabel index :=
  if h0 : index=0 then by subst index; exact (0 : RawOp.Label)
  else if h1 : index=1 then by subst index; exact ()
  else by
    have h2 : index=2 := by fin_cases index <;> simp_all
    subst index
    exact RawWrite.clearLabel 0

def initialStore (states : ℕ) (index : Fin 3) : LocalStore states index :=
  if h0 : index=0 then by subst index; exact (RawOp.before (states:=states) (fun _=>[]) none).var
  else if h1 : index=1 then by subst index; exact ()
  else by
    have h2 : index=2 := by fin_cases index <;> simp_all
    subst index
    exact (RawWrite.before (fun _=>[]) default).var

def source {states : ℕ} (machine : PaperProofs.Common.Native.RationalControllerComputation.Machine states)
    (target left right : Register) (index : Fin 3) :
    LocalLabel index → TM2.Stmt Alphabet (LocalLabel index) (LocalStore states index) :=
  if h0 : index=0 then by subst index; exact RawOp.program machine left right
  else if h1 : index=1 then by subst index; exact RawResult.program
  else by
    have h2 : index=2 := by fin_cases index <;> simp_all
    subst index
    exact RawWrite.program target

abbrev Label := CallFamily.Label LocalLabel
abbrev Store (states : ℕ) := CallFamily.Store (LocalStore states)
abbrev State (states : ℕ) := TM2.Cfg Alphabet Label (Store states)

def initialized (states : ℕ) : Store states := initialStore states

instance storeInhabited (states : ℕ) : Inhabited (Store states) := ⟨initialized states⟩

def entry (states : ℕ) (index : Fin 3) : TM2.Stmt Alphabet Label (Store states) :=
  .load (fun store=>Function.update store index (initialStore states index))
    (.goto (fun _=>CallFamily.labels LocalLabel index (startLabel index)))

def resume (states : ℕ) (index : Fin 3) : TM2.Stmt Alphabet Label (Store states) :=
  if h : index.val<2 then entry states ⟨index.val+1,by omega⟩ else .halt

/-- One finite caller for actual pair/native computation, actual singleton
header removal, and actual whole result replacement/cleanup. The family
and its finite product store are fixed before every original operand. -/
def program {states : ℕ} (machine : PaperProofs.Common.Native.RationalControllerComputation.Machine states)
    (target left right : Register) : Label → TM2.Stmt Alphabet Label (Store states) :=
  CallFamily.machine LocalLabel (LocalStore states) (source machine target left right) (resume states)

def before (states : ℕ) (contents : Stack → List Bool) : State states :=
  ⟨some (CallFamily.labels LocalLabel 0 (startLabel 0)),initialized states,contents⟩

theorem source_supports {states : ℕ}
    (machine : PaperProofs.Common.Native.RationalControllerComputation.Machine states)
    (target left right : Register) (index : Fin 3) :
    TM2.Supports (source machine target left right index) (Finset.univ : Finset (LocalLabel index)) := by
  fin_cases index
  · exact RawOp.supports machine left right
  · exact RawResult.supports
  · exact RawWrite.supports target

theorem supports {states : ℕ}
    (machine : PaperProofs.Common.Native.RationalControllerComputation.Machine states)
    (target left right : Register) :
    TM2.Supports (program machine target left right) (Finset.univ : Finset Label) := by
  apply CallFamily.supports
  · intro index
    exact source_supports machine target left right index
  · intro index
    by_cases h : index.val<2
    · simp only [resume,h,↓reduceDIte,entry,TM2.SupportsStmt]
      exact fun _=>Finset.mem_univ _
    · simp only [resume,h,↓reduceDIte,TM2.SupportsStmt]

theorem advance {states : ℕ}
    (machine : PaperProofs.Common.Native.RationalControllerComputation.Machine states)
    (target left right : Register) (index next : Fin 3) (successor : next.val=index.val+1)
    (store : Store states) (contents : Stack → List Bool) :
    TM2.step (program machine target left right)
      ⟨some (CallFamily.returnLabel LocalLabel index),store,contents⟩=
      some ⟨some (CallFamily.labels LocalLabel next (startLabel next)),
        Function.update store next (initialStore states next),contents⟩ := by
  have bound : index.val<2 := by have nextBound := next.isLt; omega
  have same : (⟨index.val+1,by omega⟩ : Fin 3)=next := Fin.ext successor.symm
  rw [← same]
  simp only [program,CallFamily.machine,CallFamily.returnLabel,resume,bound,↓reduceDIte,
    entry,TM2.step,TM2.stepAux]

theorem finish {states : ℕ}
    (machine : PaperProofs.Common.Native.RationalControllerComputation.Machine states)
    (target left right : Register) (store : Store states) (contents : Stack → List Bool) :
    TM2.step (program machine target left right) ⟨some (CallFamily.returnLabel LocalLabel 2),store,contents⟩=
      some ⟨none,store,contents⟩ := rfl

end PDROC.BitVM.Kernel.RawInstruction
