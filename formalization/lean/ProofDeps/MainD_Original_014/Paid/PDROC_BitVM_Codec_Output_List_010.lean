module

public import Paid.PDROC_BitVM_Codec_Output_List_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing

/-- The same literal pop/push drain as the frozen Boolean drain, specialized
to the fixed finalizer's four physical roles and fixed finite CountStore. -/
def flowCode (source : EmitStack) (again : CountLabel) (finish : CountStatement) : CountStatement :=
  .pop source countCapture
    (.branch (fun store => store.2.isSome)
      (.push 0 (fun store => store.2.getD false) (.goto (fun _ => again))) finish)

def flowSlots (source : EmitStack) (word target : List Bool)
    (other : EmitStack → List Bool) : EmitStack → List Bool :=
  fun role => if role = source then word else if role = 0 then target else other role

def flowState (source : EmitStack) (label : CountLabel) (store : CountStore)
    (word target : List Bool) (other : EmitStack → List Bool) : CountState :=
  ⟨some label, store, flowSlots source word target other⟩

theorem flow_update_source (source : EmitStack) (word target replacement : List Bool)
    (other : EmitStack → List Bool) :
    Function.update (flowSlots source word target other) source replacement =
      flowSlots source replacement target other := by
  funext role
  by_cases same : role = source <;> simp [flowSlots, same]

theorem flow_update_target (source : EmitStack) (different : source ≠ 0)
    (word target replacement : List Bool) (other : EmitStack → List Bool) :
    Function.update (flowSlots source word target other) 0 replacement =
      flowSlots source word replacement other := by
  funext role
  by_cases sameSource : role = source
  · subst role
    simp [flowSlots, different]
  · by_cases sameTarget : role = 0
    · subst role
      simp [flowSlots, Ne.symm different]
    · simp [flowSlots, sameSource, sameTarget]

theorem flow_cons (source : EmitStack) (different : source ≠ 0) (label : CountLabel)
    (finish : CountStatement) (store : CountStore) (bit : Bool)
    (word target : List Bool) (other : EmitStack → List Bool) :
    TM2.stepAux (flowCode source label finish) store
      (flowSlots source (bit :: word) target other) =
      flowState source label (store.1, some bit) word (bit :: target) other := by
  have sourceRead : flowSlots source (bit :: word) target other source = bit :: word := by
    simp [flowSlots]
  have targetRead : flowSlots source (bit :: word) target other 0 = target := by
    simp [flowSlots, Ne.symm different]
  simp only [flowCode, TM2.stepAux, sourceRead, List.head?_cons, List.tail_cons,
    countCapture, Option.isSome_some, Option.getD_some, Bool.cond_true]
  rw [Function.update_of_ne (Ne.symm different), targetRead, flow_update_source,
    flow_update_target source different]
  rfl

theorem flow_nil (source : EmitStack) (label : CountLabel) (finish : CountStatement)
    (store : CountStore) (target : List Bool) (other : EmitStack → List Bool) :
    TM2.stepAux (flowCode source label finish) store (flowSlots source [] target other) =
      TM2.stepAux finish (store.1, none) (flowSlots source [] target other) := by
  have sourceRead : flowSlots source [] target other source = [] := by simp [flowSlots]
  simp only [flowCode, TM2.stepAux, sourceRead, List.head?_nil, List.tail_nil,
    countCapture, Option.isSome_none, Bool.cond_false]
  rw [flow_update_source]

def flowTrace (source : EmitStack) (label : CountLabel) (finish : CountStatement)
    (other : EmitStack → List Bool) : List Bool → List Bool → CountStore → List CountState
  | [], target, store =>
      [flowState source label store [] target other,
        TM2.stepAux finish (store.1, none) (flowSlots source [] target other)]
  | bit :: word, target, store =>
      flowState source label store (bit :: word) target other ::
        flowTrace source label finish other word (bit :: target) (store.1, some bit)

theorem flow_head (source : EmitStack) (label : CountLabel) (finish : CountStatement)
    (other : EmitStack → List Bool) (word target : List Bool) (store : CountStore) :
    (flowTrace source label finish other word target store).head? =
      some (flowState source label store word target other) := by
  cases word <;> rfl

theorem flow_last (source : EmitStack) (label : CountLabel) (finish : CountStatement)
    (other : EmitStack → List Bool) (word target : List Bool) (store : CountStore) :
    (flowTrace source label finish other word target store).getLast? =
      some (TM2.stepAux finish (store.1, none)
        (flowSlots source [] (word.reverse ++ target) other)) := by
  induction word generalizing target store with
  | nil => rfl
  | cons bit word ih =>
    rw [flowTrace, List.getLast?_cons, ih]
    simp only [Option.getD_some, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem flow_length (source : EmitStack) (label : CountLabel) (finish : CountStatement)
    (other : EmitStack → List Bool) (word target : List Bool) (store : CountStore) :
    (flowTrace source label finish other word target store).length = word.length + 2 := by
  induction word generalizing target store with
  | nil => rfl
  | cons bit word ih => simp only [flowTrace, List.length_cons, ih]

theorem flow_chain (machine : CountLabel → CountStatement) (source : EmitStack)
    (different : source ≠ 0) (label : CountLabel) (finish : CountStatement)
    (code : machine label = flowCode source label finish)
    (other : EmitStack → List Bool) (word target : List Bool) (store : CountStore) :
    (flowTrace source label finish other word target store).IsChain
      (fun a b => TM2.step machine a = some b) := by
  induction word generalizing target store with
  | nil =>
    apply List.isChain_cons_cons.mpr
    constructor
    · change some (TM2.stepAux (machine label) store _) = _
      rw [code, flow_nil]
    · exact List.isChain_singleton _
  | cons bit word ih =>
    apply List.IsChain.cons (ih (bit :: target) (store.1, some bit))
    intro after member
    rw [flow_head] at member
    have same : after = flowState source label (store.1, some bit) word (bit :: target) other :=
      (Option.mem_some_iff.mp member).symm
    subst after
    change some (TM2.stepAux (machine label) store _) = _
    rw [code, flow_cons source different]

end PDROC.BitVM.Codec.OutputList
