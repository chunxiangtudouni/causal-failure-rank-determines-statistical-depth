module

public import Paid.PDROC_BitVM_Kernel_RawInstruction_041

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawInstruction

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

def lowerBefore (states : ℕ) (index : Fin 3) (contents : Stack → List Bool) :
    TM2.Cfg Alphabet (LocalLabel index) (LocalStore states index) :=
  ⟨some (startLabel index),initialStore states index,contents⟩

def entryState (states : ℕ) (index : Fin 3) (store : Store states) (contents : Stack → List Bool) : State states :=
  ⟨some (CallFamily.labels LocalLabel index (startLabel index)),
    Function.update store index (initialStore states index),contents⟩

theorem initialized_cfg (states : ℕ) (index : Fin 3) (store : Store states) (contents : Stack → List Bool) :
    CallFamily.cfg LocalLabel (LocalStore states) index (fun other=>store other.val)
      (lowerBefore states index contents)=entryState states index store contents := by
  change (⟨some (CallFamily.labels LocalLabel index (startLabel index)),
    CallFamily.split (LocalStore states) index (initialStore states index,fun other=>store other.val),contents⟩ :
    State states)=_
  congr 1

theorem initial_cfg (states : ℕ) (contents : Stack → List Bool) :
    entryState states 0 (initialized states) contents=before states contents := by
  change (⟨some (CallFamily.labels LocalLabel 0 (startLabel 0)),
    Function.update (initialized states) 0 ((initialized states) 0),contents⟩ : State states)=_
  rw [Function.update_eq_self]
  rfl

theorem lower_compute (states : ℕ) (contents : Stack → List Bool) :
    lowerBefore states 0 contents=RawOp.before contents none := rfl

theorem lower_header (states : ℕ) (contents : Stack → List Bool) :
    lowerBefore states 1 contents=RawResult.before contents := rfl

theorem lower_writer (states : ℕ) (contents : Stack → List Bool) :
    lowerBefore states 2 contents=RawWrite.before contents default := rfl

theorem overlap_last {α : Type*} (first second : List α) (middle final : α)
    (firstLast : first.getLast?=some middle) (secondHead : second.head?=some middle)
    (secondLast : second.getLast?=some final) : (first++second.tail).getLast?=some final := by
  cases second with
  | nil => simp only [List.head?_nil,reduceCtorEq] at secondHead
  | cons start rest =>
    have same : start=middle := Option.some.inj secondHead
    subst start
    cases rest with
    | nil =>
      have same : middle=final := Option.some.inj secondLast
      simpa only [List.tail_cons,List.append_nil,same] using firstLast
    | cons next later =>
      rw [List.tail_cons,List.getLast?_append_cons]
      simpa only [List.getLast?_cons_cons] using secondLast

end PDROC.BitVM.Kernel.RawInstruction
