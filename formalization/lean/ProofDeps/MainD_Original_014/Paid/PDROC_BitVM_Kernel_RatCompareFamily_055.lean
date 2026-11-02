module

public import Paid.PDROC_BitVM_Kernel_RatCompare_051

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RatCompare

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

def lowerBefore (states : ℕ) (index : Fin 4) (contents : Stack → List Bool) :
    TM2.Cfg Alphabet (LocalLabel index) (LocalStore states index) :=
  ⟨some (startLabel index),initialStore states index,contents⟩

def entryState (states : ℕ) (index : Fin 4) (store : Store states) (contents : Stack → List Bool) : State states :=
  ⟨some (CallFamily.labels LocalLabel index (startLabel index)),
    Function.update store index (initialStore states index),contents⟩

def observedState (states : ℕ) (comparison : Comparison) (store : Store states)
    (contents : Stack → List Bool) : State states :=
  ⟨some (CallFamily.labels LocalLabel 2 (startLabel 2)),
    Function.update store 2 (CompareFlag.flag comparison (store 1)),contents⟩

theorem selected_store (states : ℕ) (index : Fin 4) (active : LocalStore states index)
    (saved : CallFamily.Saved (LocalStore states) index) :
    CallFamily.split (LocalStore states) index (active,saved) index=active := by
  simp [CallFamily.split,Equiv.piSplitAt]

theorem initialized_cfg (states : ℕ) (index : Fin 4) (store : Store states) (contents : Stack → List Bool) :
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

theorem observed_cfg (states : ℕ) (comparison : Comparison) (store : Store states) (contents : Stack → List Bool) :
    CallFamily.cfg LocalLabel (LocalStore states) 2 (fun other=>store other.val)
      (BoolCell.before contents (CompareFlag.flag comparison (store 1)))=
      observedState states comparison store contents := by
  change (⟨some (CallFamily.labels LocalLabel 2 (startLabel 2)),
    CallFamily.split (LocalStore states) 2 (CompareFlag.flag comparison (store 1),fun other=>store other.val),contents⟩ :
    State states)=_
  congr 1

theorem advance_zero {states : ℕ} (machine : Machine states) (comparison : Comparison) (target left right : Register)
    (store : Store states) (contents : Stack → List Bool) :
    TM2.step (program machine comparison target left right)
      ⟨some (CallFamily.returnLabel LocalLabel 0),store,contents⟩=
      some (entryState states 1 store contents) := rfl

theorem advance_observed {states : ℕ} (machine : Machine states) (comparison : Comparison) (target left right : Register)
    (store : Store states) (contents : Stack → List Bool) :
    TM2.step (program machine comparison target left right)
      ⟨some (CallFamily.returnLabel LocalLabel 1),store,contents⟩=
      some (observedState states comparison store contents) := rfl

theorem advance_two {states : ℕ} (machine : Machine states) (comparison : Comparison) (target left right : Register)
    (store : Store states) (contents : Stack → List Bool) :
    TM2.step (program machine comparison target left right)
      ⟨some (CallFamily.returnLabel LocalLabel 2),store,contents⟩=
      some (entryState states 3 store contents) := rfl

theorem finish {states : ℕ} (machine : Machine states) (comparison : Comparison) (target left right : Register)
    (store : Store states) (contents : Stack → List Bool) :
    TM2.step (program machine comparison target left right)
      ⟨some (CallFamily.returnLabel LocalLabel 3),store,contents⟩=some ⟨none,store,contents⟩ := rfl

end PDROC.BitVM.Kernel.RatCompare
